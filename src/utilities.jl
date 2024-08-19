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


#####################################################
#########  GTSP Utilities ###########################

""" tour type that stores the order array and the length of the tour
"""
mutable struct Tour
	tour::Array{Int64,1}
	cost::Int64
end

""" return the vertex before tour[i] on tour """
@inline function prev_tour(tour, i)
	# 如果i！=1，返回tour[i-1]
	i != 1 && return tour[i - 1]
	# 由于路径是环形的，所以当i=1时，返回tour的最后一个元素
	return tour[length(tour)]
end

######################################################
#############  Randomizing tour before insertions ####

""" some insertions break tie by taking first minimizer -- this
randomization helps avoid getting stuck choosing same minimizer """
function pivot_tour!(tour::Array{Int64,1})
	# 从路径中选择一个随机位置作为巡回路径起点
	pivot = rand(1:length(tour))
	tour = [tour[pivot:end]; tour[1:pivot-1]]
end


function randomize_sets!(sets::Array{Any, 1}, sets_to_insert::Array{Int64, 1})
	# 随机打乱sets_to_insert中集合的节点
	for i in sets_to_insert
		shuffle!(sets[i])
	end
end

"""  create an array containing the set number for each vertex """
function findmember(num_vertices::Int64, sets::Array{Any, 1})
	# 为每个节点找到所属的集合
	member = zeros(Int64, num_vertices)
    num_verts = 0
    for i = 1:length(sets)
        set = sets[i]
        num_verts += length(set)
        for vertex in set
			if member[vertex] != 0
				error("vertex ", vertex, " belongs to more than one set")
			else
				member[vertex] = i
			end
        end
    end
    return member
end


struct Distsv
	set_vert::Array{Int64, 2}
	vert_set::Array{Int64,2}
	min_sv::Array{Int64, 2}
end

"""
Computes the minimum distance between each set and each vertex
Also compute the minimum distance from a set to a vertex, ignoring direction
This is used in insertion to choose the next set.
"""
function set_vertex_dist(dist::Array{Int64, 2}, num_sets::Int, member::Array{Int64,1})
    numv = size(dist, 1)
    dist_set_vert = typemax(Int64) * ones(Int64, num_sets, numv)
	mindist = typemax(Int64) * ones(Int64, num_sets, numv)
	dist_vert_set = typemax(Int64) * ones(Int64, numv, num_sets)

	for i = 1:numv
        for j = 1:numv
			set = member[j]
			if dist[j,i] < dist_set_vert[set, i]
				dist_set_vert[set, i] = dist[j,i]
			end
			if dist[j,i] < mindist[set, i]  # dist from set containing j to vertex i
				mindist[set, i] = dist[j, i]
			end
			set = member[i]
			if dist[j,i] < dist_vert_set[j, set]  # dist from j to set containing i
				dist_vert_set[j, set] = dist[j,i]
			end
			if dist[j,i] < mindist[set,j] # record as distance from set containing i to j
				mindist[set,j] = dist[j,i]
			end
		end
	end
    return Distsv(dist_set_vert, dist_vert_set, mindist)
end



function set_vertex_distance(dist::Array{Int64, 2}, sets::Array{Any, 1})
    """
	Computes the minimum distance between each set and each vertex
	"""
    numv = size(dist, 1)
    nums = length(sets)
    dist_set_vert = typemax(Int64) * ones(Int64, nums, numv)
	# dist_vert_set = typemax(Int64) * ones(Int64, numv, nums)
    for i = 1:nums
        for j = 1:numv
			for k in sets[i]
				newdist = min(dist[k, j], dist[j, k])
				dist_set_vert[i,j] > newdist && (dist_set_vert[i,j] = newdist)
			end
        end
    end
    return dist_set_vert
end


""" Find the set with the smallest number of vertices """
function min_set(sets::Array{Any, 1})
	# 找到节点数量最少的集合在sets中的索引
    min_size = length(sets[1])
	min_index = 1
    for i = 2:length(sets)
		set_size = length(sets[i])
		if set_size < min_size
			min_size = set_size
			min_index = i
		end
	end
	return min_index
end


############################################################
############ Trial acceptance criteria #####################

"""
decide whether or not to accept a trial based on simulated annealing criteria
"""
function accepttrial(trial_cost::Int64, current_cost::Int64, temperature::Float64)
    # 如果新解小于等于旧解，接受新解
	if trial_cost <= current_cost
        accept_prob = 2.0
	# 反之接受旧解的概率accept_prob = exp((current_cost - trial_cost)/temperature)
	else
        accept_prob = exp((current_cost - trial_cost)/temperature)
    end
    return (rand() < accept_prob ? true : false)
end


"""
decide whether or not to accept a trial based on simple probability
"""
function accepttrial_noparam(trial_cost::Int64, current_cost::Int64, prob_accept::Float64)
	# 如果新解小于等于旧解，接受新解
    if trial_cost <= current_cost
        return true
	end
	# 接受旧解的概率为prob_accept
	return (rand() < prob_accept ? true : false)
end


###################################################
################ Tour checks ######################

"""  Compute the length of a tour  """
@inline function tour_cost(tour::Array{Int64,1}, dist::Array{Int64,2})
	# 计算巡回路径的长度
    tour_length = dist[tour[end], tour[1]]
    @inbounds for i in 1:length(tour)-1
    	tour_length += dist[tour[i], tour[i+1]]
    end
    return tour_length
end


"""
Checks if a tour is feasible in that it visits each set exactly once.
"""
function tour_feasibility(tour::Array{Int64,1}, membership::Array{Int64,1}, num_sets::Int64)
	# 检查巡回路径是否可行，即是否每个集合都被访问一次
    length(tour) != num_sets && return false
	# 初始化bool数组长度为集合数量，均为false，用于检查每个集合是否被访问一次
    set_test = falses(num_sets)
	# 遍历巡回路径中的每个节点，检查集合是否被访问一次
    for v in tour
        set_v = membership[v]
		if set_test[set_v]
			return false  # a set is visited twice in the tour
		end
		set_test[set_v] = true
    end
	# 检查集合是否都被访问一次
    for visited_set in set_test
        !visited_set && return false
    end
    return true
end


#####################################################
#############  Incremental Shuffle ##################

@inline function incremental_shuffle!(a::AbstractVector, i::Int)
	# 从数组a中选择大于序号i的元素，与a[i]交换
    j = i + floor(Int, rand() * (length(a) + 1 - i))
   	a[j], a[i] = a[i], a[j]
	# 返回原来的a[j],现在的a[i]
	return a[i]
end


""" rand_select for randomize over all minimizers """
@inline function rand_select(a::Array{Int64, 1}, val::Int)
	# 将数组a中等于val的元素的索引存储在inds中，然后从inds中随机选择一个索引
	inds = Int[]
	@inbounds for i=1:length(a)
		a[i] == val && (push!(inds, i))
	end
	return rand(inds)
end
