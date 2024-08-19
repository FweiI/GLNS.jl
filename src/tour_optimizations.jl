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
Sequentially moves each vertex to its best point on the tour.
Repeats until no more moves can be found
"""
function moveopt!(tour::Array{Int64, 1}, dist::Array{Int64, 2}, sets::Array{Any, 1}, 
				  member::Array{Int64,1}, setdist::Distsv)
    improvement_found = true
    number_of_moves = 0
    start_position = 1

    @inbounds while improvement_found && number_of_moves < 10
        improvement_found = false
        for i = start_position:length(tour)
			# 选择tour[i]节点
            select_vertex = tour[i]
			# 计算移除tour[i]的代价
            delete_cost = removal_cost(tour, dist, i)
			# 获取tour[i]节点所属集合序号
			set_ind = member[select_vertex]
			# 移除tour[i]节点
            splice!(tour, i)  # remove vertex from tour

			# 此时sets[set_ind] = P_T\P_V，算出该集合所选插入节点、插入位置、以及插入代价
            v, pos, cost = insert_cost_lb(tour, dist, sets[set_ind], set_ind, setdist, 
										  select_vertex, i, delete_cost)
			# 插入节点
            insert!(tour, pos, v)
            # 如果插入代价小于删除代价，说明找到了更优的路径
            if cost < delete_cost
                improvement_found = true
                number_of_moves += 1
				# 如果路径有所改善，从移除位置后或插入位置后开始重新寻找优化节点
                start_position = min(pos, i) # start looking for swaps where tour change began
                break
            end
        end
    end
end


function moveopt_rand!(tour::Array{Int64, 1}, dist::Array{Int64, 2}, sets::Array{Any, 1}, 
				  member::Array{Int64,1}, iters::Int, setdist::Distsv)
	# 创建一个从1到length(tour)且长度为length(tour)的数组
	tour_inds = collect(1:length(tour))
	# 限制循环次数为iter->N_move
	@inbounds for i = 1:iters # i = rand(1:length(tour), iters)
		# 从tour_inds中“随机选择“一个索引
		i = incremental_shuffle!(tour_inds, i)
		# 根据索引获取tour中的节点
		select_vertex = tour[i]
		
		# 计算移除tour[i]的代价
		delete_cost = removal_cost(tour, dist, i)
	    set_ind = member[select_vertex]
		splice!(tour, i)  # remove vertex from tour
		# 此时sets[set_ind] = P_T\P_V，算出该集合所选插入节点、插入位置、以及插入代价
	    v, pos, cost = insert_cost_lb(tour, dist, sets[set_ind], set_ind, setdist, 
								      select_vertex, i, delete_cost)
		insert!(tour, pos, v)
    end
end


"""
compute the cost of inserting vertex v into position i of tour
"""
@inline function insert_cost_lb(tour::Array{Int64,1}, dist::Array{Int64,2}, set::Array{Int64, 1}, setind::Int, 
						   setdist::Distsv, bestv::Int, bestpos::Int, best_cost::Int)
	# 遍历部分巡回轨迹上的节点
    @inbounds for i = 1:length(tour)
		# v1为tour上i先前的一个节点（论文中的Vi中的x），tour[i]为当前节点（论文中的Vi中的y）
		v1 = prev_tour(tour, i) # first check lower bound
		# 根据论文3.4的公式计算该位置插入代价的下界lb = dist(Vi,x)+dist(Vi,y)-w(x,y)
		# 这里与论文不一致，原论文的dist(Vi,u)应为代码中的min_sv(Vi,u)，但并不影响
		lb = setdist.vert_set[v1, setind] + setdist.set_vert[setind, tour[i]] - dist[v1, tour[i]]
		lb > best_cost && continue
		
		# 遍历Vi中的v
		for v in set
	        insert_cost = dist[v1, v] + dist[v, tour[i]] - dist[v1, tour[i]]
	        if insert_cost < best_cost
				best_cost = insert_cost
				bestv = v
				bestpos = i
	        end
		end
    end
    return bestv, bestpos, best_cost
end


"""
determine the cost of removing the vertex at position i in the tour
"""
@inline function removal_cost(tour::Array{Int64, 1}, dist::Array{Int64, 2}, i::Int64)
	# 计算删除tour[i]的代价
	# 注意巡回轨迹边界
    if i == 1
        return dist[tour[end], tour[i]] + dist[tour[i], tour[i+1]] - dist[tour[end], tour[i+1]]
    elseif i == length(tour)
        return dist[tour[i-1], tour[i]] + dist[tour[i], tour[1]] - dist[tour[i-1], tour[1]]
    else
        return dist[tour[i-1], tour[i]] + dist[tour[i], tour[i+1]] - dist[tour[i-1], tour[i+1]]
	end
end


""" repeatedly perform moveopt and reopt_tour until there is no improvement """
function opt_cycle!(current::Tour, dist::Array{Int64,2}, sets::Array{Any, 1}, 
					member::Array{Int64,1}, param::Dict{Symbol, Any}, setdist::Distsv, use)
	# 论文5.5
	current.cost = tour_cost(current.tour, dist)
	prev_cost = current.cost
	# 循环5次？
	for i=1:5
		# 奇数次 reopt_tour 路径集合顺序不变，动态规划选取最优节点
		if i % 2 == 1
			current.tour = reopt_tour(current.tour, dist, sets, member, param)
		# 偶数次 “fast”模式 或 局部优化
		elseif param[:mode] == "fast" || use == "partial"
			# param[:max_removals] -> N_move
			moveopt_rand!(current.tour, dist, sets, member, param[:max_removals], setdist)
		# 偶数次 “default”、“slow”模式 或 全局优化
		else
			moveopt!(current.tour, dist, sets, member, setdist)
		end
		
		current.cost = tour_cost(current.tour, dist)
		# 如果连续迭代过程中没有改善或者在局部优化模式，提前终止
		if i > 1 && (current.cost >= prev_cost || use == "partial")
			return
		end
		prev_cost = current.cost
	end	
end


"""
Given an ordering of the sets, this alg performs BFS to find the 
optimal vertex in each set
"""
function reopt_tour(tour::Array{Int64,1}, dist::Array{Int64,2}, sets::Array{Any, 1}, 
					member::Array{Int64,1}, param::Dict{Symbol, Any})
	# 论文5.5 Re-Optimize 保持巡回路径的集合顺序，动态规划选取最优节点
	
    best_tour_cost = tour_cost(tour, dist)
	new_tour = copy(tour)
	# 找到最小集合在轨迹上的索引
	min_index = min_setv(tour, sets, member, param)	
	# 重新构建巡回路径，使得最小集合在轨迹上的索引为1
    tour = [tour[min_index:end]; tour[1:min_index-1]]

    prev = zeros(Int64, param[:num_vertices])   # initialize cost_to_come
    cost_to_come = zeros(Int64, param[:num_vertices])
	# 从最小集合开始，遍历内部每个节点
    @inbounds for start_vertex in sets[member[tour[1]]]
		# 动态规划，计算以start_vertex为起点的优化路径
		# prev存储路径上每个节点的前一个节点，cost_to_come存储到达每个节点的最小花费
 		relax_in!(cost_to_come, dist, prev, Int64[start_vertex], sets[member[tour[2]]])
        for i = 3:length(tour)  # cost to get to ith set on path through (i-1)th set
            relax_in!(cost_to_come, dist, prev, sets[member[tour[i-1]]], sets[member[tour[i]]])
        end
        # 获取reopt_tour的最小花费，以及巡回路径最后集合中优化节点
        tour_cost, start_prev = relax(cost_to_come, dist, sets[member[tour[end]]], start_vertex)
		# 如果reopt_tour的最小花费小于原来的最小花费，重新构建路径
        if tour_cost < best_tour_cost   # reconstruct the path
			best_tour_cost = tour_cost
            new_tour = extract_tour(prev, start_vertex, start_prev)
        end
    end
	return new_tour
end


""" Find the set with the smallest number of vertices """
function min_setv(tour::Array{Int64, 1}, sets::Array{Any, 1}, member::Array{Int64, 1},  param::Dict{Symbol, Any})
	# param中的min_set为最小集合的节点数，min_set为最小集合在sets中的索引
	min_set = param[:min_set]
	# 返回最小集合在轨迹上的的索引
	@inbounds for i = 1:length(tour)
		member[tour[i]] == min_set && return i
	end
	return 1
end


"""
extracting a tour from the prev pointers.
"""
function extract_tour(prev::Array{Int64,1}, start_vertex::Int64, start_prev::Int64)
	# 将末尾集合的节点添加到路径中
    tour = [start_vertex]
	# 逐步向前寻找reopt_tour的路径上的节点
    vertex_step = start_prev
    while prev[vertex_step] != 0
        push!(tour, vertex_step)
        vertex_step = prev[vertex_step]
    end
    return reverse(tour)
end


"""
outputs the new cost and prev for vertex v2 after relaxing
does not actually update the cost
"""
@inline function relax(cost::Array{Int64, 1}, dist::Array{Int64, 2}, set1::Array{Int64, 1}, v2::Int64)
	# 对于末尾节点v2，存在v1 \in set1，使得(v1,v2)的花费最小
	v1 = set1[1]
	min_cost = cost[v1] + dist[v1, v2]
	min_prev = v1
    @inbounds for i = 2:length(set1)
		v1 = set1[i]
		newcost = cost[v1] + dist[v1, v2]
        if min_cost > newcost
            min_cost, min_prev = newcost, v1
        end
    end
	# 返回最小花费和前一个节点
    return min_cost, min_prev
end


"""
relaxes the cost of each vertex in the set set2 in-place.
"""
@inline function relax_in!(cost::Array{Int64, 1}, dist::Array{Int64, 2}, prev::Array{Int64, 1}, 
				 set1::Array{Int64, 1}, set2::Array{Int64, 1})
	# 对于任意v2 \in set2，存在v1 \in set1，使得(v1,v2)的花费最小

	# 循环遍历set2中的每个节点
	@inbounds for v2 in set2
		# 遍历v1，计算到v2最小花费
		v1 = set1[1]
		cost[v2] = cost[v1] + dist[v1, v2]
		prev[v2] = v1
        for i = 2:length(set1)
			v1 = set1[i]
			newcost = cost[v1] + dist[v1, v2]
            if cost[v2] > newcost
				cost[v2], prev[v2] = newcost, v1
            end
        end
    end
end