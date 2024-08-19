# Copyright 2017 Stephen L. Smith and Frank Imeson
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""
Select a removal and an insertion method using powers, and then perform
removal followed by insertion on tour.  Operation done in place.
"""
function remove_insert(current::Tour, best::Tour, dist::Array{Int64,2}, member::Array{Int64,1},
						setdist::Distsv, sets::Array{Any,1},
						powers, param::Dict{Symbol,Any}, phase::Symbol)
	# make a new tour to perform the insertion and deletion on
    trial = Tour(copy(current.tour), current.cost)
	# 从路径中选择一个随机位置作为巡回路径起点
	pivot_tour!(trial.tour)
	# 随机选择删除节点的数量N_r
	num_removals = rand(param[:min_removals]:param[:max_removals])

	# 根据时期、总权重选择删除启发式函数
	removal = power_select(powers["removals"], powers["removal_total"], phase)
	# 根据启发式函数选择删除节点 sets_to_insert->P_V/P_T
	if removal.name == "distance"
		sets_to_insert = distance_removal!(trial.tour, dist, num_removals, member, removal.value)
    elseif removal.name == "worst"
		sets_to_insert = worst_removal!(trial.tour, dist, num_removals, member, removal.value)
	else
		sets_to_insert = segment_removal!(trial.tour, num_removals, member)
	end

	# 随机化P_V/P_T中的节点
	randomize_sets!(sets, sets_to_insert)
	# 根据时期、总权重选择插入启发式函数
	insertion = power_select(powers["insertions"], powers["insertion_total"], phase)
	# 根据时期、总权重选择噪声阈值
	noise = power_select(powers["noise"], powers["noise_total"], phase)
	# 根据启发式函数与噪声阈值选择插入启发式函数
	if insertion.name == "cheapest"
		cheapest_insertion!(trial.tour, sets_to_insert, dist, setdist, sets)
	else
		randpdf_insertion!(trial.tour, sets_to_insert, dist, setdist, sets, insertion.value, noise)
	end
	rand() < param[:prob_reopt] && opt_cycle!(trial, dist, sets, member, param, setdist, "partial")

	# update power scores for remove and insert
	score = 100 * max(current.cost - trial.cost, 0)/current.cost
	insertion.scores[phase] += score
	insertion.count[phase] += 1
	removal.scores[phase] += score
	removal.count[phase] += 1
	noise.scores[phase] += score
	noise.count[phase] += 1
	return trial
end


"""
Select an integer between 1 and num according to
and exponential distribution with lambda = power
# goes from left of array if power is positive
# and right of array if it is negative
"""
function select_k(num::Int64, power::Float64)
	# 根据该函数前的注释，abs(power)越大，lambda越小，k越小；反之，k越大
	# power>0,选择右侧第k；power<0,选择左侧第k个
	# base = (1/2)^abs(power)->lambda
	base = (1/2)^abs(power)
	# (1 - base^num)/(1 - base) is sum of geometric series
	# 对所有序列的概率权重base^num进行求和
	rand_select = (1 - base^num)/(1 - base) * rand()
	bin = 1
	@inbounds for k = 1:num
		if rand_select < bin
			return (power >= 0 ? (num - k + 1) : k)
		end
		rand_select -= bin
		bin *= base
	end
	return (power >=0 ? num : 1)
end


"""
selecting a random k in 1 to length(weights) according to power
and then selecting the kth smallest element in weights
"""
function pdf_select(weights::Array{Int64,1}, power::Float64)
	# 比论文中多了些许实现细节，比如相同值的节点再随机选取
	# (0.5)^abs(power) -> lambda
	# power>0,选择右侧第k个；power<0,选择左侧第k个
	# 如果lambda=1，随机选择一个节点
    power == 0.0 && return rand(1:length(weights))
	# 如果lambda->0，power > 0，右侧第一个
    power > 9.0 && return rand_select(weights, maximum(weights))
	# 如果lambda->0，power < 0，左侧第一个
    power < - 9.0 && return rand_select(weights, minimum(weights))

	# 如果power在(-9,9)之间，选择第k小的节点
	k = select_k(length(weights), power)
	k == 1 && return rand_select(weights, minimum(weights))
	k == length(weights) && return rand_select(weights, maximum(weights))
	# 如果k不是排序边界点，则不得不排序后选取
	val = partialsort(weights, k)

	# 再随机选取一个等于val的节点
	return rand_select(weights, val)
end


"""  choose set with pdf_select, and then insert in best place with noise  """
function randpdf_insertion!(tour::Array{Int64,1}, sets_to_insert::Array{Int64,1},
							dist::Array{Int64, 2}, setdist::Distsv,
							sets::Array{Any, 1}, power::Float64, noise::Power)

    mindist = [typemax(Int64) for i=1:length(sets_to_insert)]
    @inbounds for i = 1:length(sets_to_insert)
        set = sets_to_insert[i]
        for vertex in tour
            if setdist.min_sv[set, vertex] < mindist[i]
                mindist[i] = setdist.min_sv[set, vertex]
            end
        end
    end
    new_vertex_in_tour = 0

    @inbounds while length(sets_to_insert) > 0
        if new_vertex_in_tour != 0
            for i = 1:length(sets_to_insert)
                set = sets_to_insert[i]
                if setdist.min_sv[set, new_vertex_in_tour] < mindist[i]
                    mindist[i] = setdist.min_sv[set, new_vertex_in_tour]
                end
            end
        end
        set_index = pdf_select(mindist, power) # select set to insert from pdf
        # find the closest vertex and the best insertion in that vertex
        nearest_set = sets_to_insert[set_index]
		if noise.name == "subset"
			bestv, bestpos = insert_subset_lb(tour, dist, sets[nearest_set], nearest_set,
											  setdist, noise.value)
		else
			bestv, bestpos =
					insert_lb(tour, dist, sets[nearest_set], nearest_set, setdist, noise.value)
		end
        insert!(tour, bestpos, bestv)  # perform the insertion
        new_vertex_in_tour = bestv
        # remove the inserted set from data structures
        splice!(sets_to_insert, set_index)
        splice!(mindist, set_index)
    end
end

"""
choose vertex that can be inserted most cheaply, and insert it in that position
"""
function cheapest_insertion!(tour::Array{Int64,1}, sets_to_insert::Array{Int64,1}, dist::Array{Int64, 2}, setdist::Distsv, sets::Array{Any, 1})
	while length(sets_to_insert) > 0
        best_cost = typemax(Int64)
        best_v = 0
        best_pos = 0
        best_set = 0
		# 遍历P_T\P_V中的集合
        for i = 1:length(sets_to_insert)
			# 选取集合Vi
            set_ind = sets_to_insert[i]
            # find the best place to insert the vertex
            best_v, best_pos, cost = insert_cost_lb(tour, dist, sets[set_ind], set_ind, setdist, best_v, best_pos, best_cost)
			if cost < best_cost
				best_set = i
				best_cost = cost
			end
        end
        # now, perform the insertion
        insert!(tour, best_pos, best_v)
        # remove the inserted set from data structures
        splice!(sets_to_insert, best_set)
    end
end


"""
Given a tour and a set, this function finds the vertex in the set with minimum
insertion cost, along with the position of this insertion in the tour.  If
best_position is i, then vertex should be inserted between tour[i-1] and tour[i].
"""
@inline function insert_lb(tour::Array{Int64,1}, dist::Array{Int64,2}, set::Array{Int64, 1}, setind::Int, setdist::Distsv, noise::Float64)
	# set为论文中的集合Vi，setind为集合Vi在sets中的索引
	best_cost = typemax(Int64)
	bestv = 0
	bestpos = 0
	# 遍历轨迹上的可插入位置，寻找合适的插入位置
	@inbounds for i = 1:length(tour)
		# v1为tour上i先前的一个节点（论文中的Vi中的x），tour[i]为当前节点（论文中的Vi中的y）
		v1 = prev_tour(tour, i)
		# 根据论文3.4的公式计算该位置插入代价的下界lb = dist(Vi,x)+dist(Vi,y)-w(x,y)
		# 这里与论文不一致，原论文的dist(Vi,u)应为代码中的min_sv(Vi,u)，但并不影响
		lb = setdist.vert_set[v1, setind] + setdist.set_vert[setind, tour[i]] - dist[v1, tour[i]]
		# 判断lb与w(bestx,bestv)+w(bestv,besty)-w(bestx,besty)关系
		# 如果下界大于当前最优代价，则跳过
		lb > best_cost && continue
		# 反之，在该位置插入的代价可能优于当前最优代价，寻找合适的v
		# 遍历集合Vi中的节点，计算(1+rand)*(w(v,x)+w(v,y)-w(x,y))，更新w(bestx,bestv) + w(bestv,besty) - w(bestx,besty)
		for v in set
	        insert_cost = dist[v1, v] + dist[v, tour[i]] - dist[v1, tour[i]]
			noise > 0.0 && (insert_cost += round(Int64, noise * rand() * abs(insert_cost)))
			if insert_cost < best_cost
				# 更新当前最优代价、节点、位置
				best_cost = insert_cost
				bestv = v
				bestpos = i
	        end
		end
    end
    return bestv, bestpos
end


@inline function insert_subset_lb(tour::Array{Int64,1}, dist::Array{Int64,2}, set::Array{Int64, 1},
							setind::Int, setdist::Distsv, noise::Float64)
	best_cost = typemax(Int64)
	bestv = 0
	bestpos = 0
	tour_inds = collect(1:length(tour))

	@inbounds for i = 1:ceil(Int64, length(tour) * noise)
		i = incremental_shuffle!(tour_inds, i)
		v1 = prev_tour(tour, i)
		lb = setdist.vert_set[v1, setind] + setdist.set_vert[setind, tour[i]] - dist[v1, tour[i]]
		lb > best_cost && continue

		for v in set
	        insert_cost = dist[v1, v] + dist[v, tour[i]] - dist[v1, tour[i]]
	        if insert_cost < best_cost
				best_cost = insert_cost
				bestv = v
				bestpos = i
	        end
		end
    end
    return bestv, bestpos
end


############ Initial Tour Construction ##########################

"""build tour from scratch on a cold restart"""
function initial_tour!(lowest::Tour, dist::Array{Int64, 2}, sets::Array{Any, 1}, setdist::Distsv, trial_num::Int64, param::Dict{Symbol,Any})
	# 初始化还未插入到轨迹的集合数组
	sets_to_insert = collect(1:param[:num_sets])
	best = Tour(Int64[], typemax(Int64))

	# compute random initial tour only if past first trial
	# in this case, randomly choose between random and insertion tour.
	# 根据配置参数、冷启动次数、随机数，选择 洗牌随机 或 随机插入（类似于插入启发式）生成初始解
	if param[:init_tour] == "rand" && (trial_num > 1) && (rand() < 0.5)
		# 洗牌随机均匀选取节点生成初始解
		random_initial_tour!(best.tour, sets_to_insert, dist, sets)
	else
		# 随机插入（类似于插入启发式）生成初始解
		random_insertion!(best.tour, sets_to_insert, dist, sets, setdist)
	end
	best.cost = tour_cost(best.tour, dist)
	lowest.cost > best.cost && (lowest = best)
	return best
end


"""
Randomly shuffle the sets, and then insert the best vertex from each set back into
the tour where sets are considered in shuffled order.
"""
function random_insertion!(tour::Array{Int64,1}, sets_to_insert::Array{Int64,1}, dist::Array{Int64, 2}, sets::Array{Any, 1}, setdist::Distsv)
    shuffle!(sets_to_insert)  # randomly permute the sets
    for set in sets_to_insert
        # only have to compute the insert cost for the changed portion of the tour
		# 如果当前巡回为空，则从打乱的集合中选取一个节点插入到轨迹中，记录节点在轨迹中的位置
        if isempty(tour)
            best_vertex = rand(sets[set])
            best_position = 1
		# 如果当前巡回不为空，则根据插入启发式函数选取一个节点插入到轨迹中，记录节点在轨迹中的位置
        else
            best_vertex, best_position = insert_lb(tour, dist, sets[set], set, setdist, 0.75)
        end
        # now, perform the insertion
		# 将选取的节点插入到轨迹中的合适位置
        insert!(tour, best_position, best_vertex)
    end
end


"""
Randomly shuffle the sets, and then insert the best vertex from each set back into
the tour where sets are considered in shuffled order.
"""
function random_initial_tour!(tour::Array{Int64,1}, sets_to_insert::Array{Int64,1}, dist::Array{Int64, 2}, sets::Array{Any, 1})
    shuffle!(sets_to_insert)
    for set in sets_to_insert
		# 从打乱的集合中随机选取一个节点插入到轨迹中
		push!(tour, rand(sets[set]))
    end
end


######################### Removals ################################
"""
Remove the vertices randomly, but biased towards those that add the most length to the
tour.  Bias is based on the power input.  Vertices are then selected via pdf select.
"""
function worst_removal!(tour::Array{Int64,1}, dist::Array{Int64, 2}, num_to_remove::Int64, member::Array{Int64,1}, power::Float64)
    deleted_sets = Array{Int}(undef, 0)
	while length(deleted_sets) < num_to_remove
		# 计算每个节点的删除代价（如果移除tour[i]，是否只用更新前后两个节点的removal_costs）
		removal_costs = worst_vertices(tour, dist)
		# 根据power判断从removal_costs选取移除节点位置 
		ind = pdf_select(removal_costs, power)
		set_to_delete = member[tour[ind]]

        # perform the deletion
        push!(deleted_sets, set_to_delete)
		splice!(tour, ind)
	end
	# deleted_sets -> P_V/P_T
    return deleted_sets
end


""" removing a single continuos segment of the tour of size num_remove """
function segment_removal!(tour::Array{Int64, 1}, num_to_remove::Int64, member::Array{Int64,1})
	# 从路径中随机选取一个节点，然后删除其后连续的num_to_remove个节点
	i = rand(1:length(tour))
	deleted_sets = Array{Int}(undef, 0)
	while length(deleted_sets) < num_to_remove
		i > length(tour) && (i = 1)
		push!(deleted_sets, member[tour[i]])
		splice!(tour, i)
	end
	# deleted_sets -> P_V/P_T
	return deleted_sets
end


"""  pick a random vertex, and delete its closest neighbors  """
function distance_removal!(tour::Array{Int64,1}, dist::Array{Int64, 2}, num_to_remove::Int64, member::Array{Int64,1}, power::Float64)
    # 论文4.2 0.5^abs(power)->lambda, deleted_sets->P_V/P_T, deleted_vertices->V_removed
	deleted_sets = Array{Int}(undef, 0)
    deleted_vertices = Array{Int}(undef, 0)

	# 均匀随机从轨迹中选取第一个删除节点
    seed_index = rand(1:length(tour))
	# 将v_seed从属的集合加入到P_V/P_TV中
    push!(deleted_sets, member[tour[seed_index]])
	# 将v_seed加入到V_removed中
    push!(deleted_vertices, tour[seed_index])
	# 从轨迹中删除v_seed
    splice!(tour, seed_index)

	# 删除节点的数量小于num_to_remove时，循环删除节点
    while length(deleted_sets) < num_to_remove
        # 随机从已删除节点中选取一个节点
        seed_vertex = rand(deleted_vertices)
		# 计算seed_vertex与tour中最小距离的节点
        mindist = zeros(Int64, length(tour))
        for i = 1:length(tour)
			mindist[i] = min(dist[seed_vertex, tour[i]], dist[tour[i], seed_vertex])
        end
		# 根据power判断从mindis选取移除节点位置
        del_index = pdf_select(mindist, power)
        push!(deleted_sets, member[tour[del_index]])
        push!(deleted_vertices, tour[del_index])
        splice!(tour, del_index)
    end
	# deleted_sets -> P_V/P_T
    return deleted_sets
end


"""
determine the cost of removing each vertex from the tour, given that all others remain.
"""
function worst_vertices(tour::Array{Int64, 1}, dist::Array{Int64, 2})
	# removal_cost存储了删除每个节点的代价
    removal_cost = zeros(Int64, length(tour))
    @inbounds for i = 1:length(tour)
		# 注意巡回路径的首尾节点
        if i == 1
            removal_cost[i] = dist[tour[end], tour[i]] +
								dist[tour[i], tour[i+1]] - dist[tour[end], tour[i+1]]
        elseif i == length(tour)
            removal_cost[i] = dist[tour[i-1], tour[i]] +
								dist[tour[i], tour[1]] - dist[tour[i-1], tour[1]]
        else
            removal_cost[i] = dist[tour[i-1], tour[i]] +
								dist[tour[i], tour[i+1]] - dist[tour[i-1], tour[i+1]]
		end
    end
    return removal_cost
end
