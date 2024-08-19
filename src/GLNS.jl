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
module GLNS
export solver
using Random
include("utilities.jl")
include("parse_print.jl")
include("tour_optimizations.jl")
include("adaptive_powers.jl")
include("insertion_deletion.jl")
include("parameter_defaults.jl")

"""
Main GTSP solver, which takes as input a problem instance and
some optional arguments
"""
function solver(problem_instance; args...)
	###### Read problem data and solver settings ########
	# 根据路径信息读取文件，获取节点数量、集合数量、集合信息（存有节点）、节点间距离矩阵、节点所属集合信息
	# 节点间的距离矩阵dist是一个Int64的二维数组？
	num_vertices, num_sets, sets, dist, membership = read_file(problem_instance)
	# 根据args参数设置GTSP求解器的参数
	param = parameter_settings(num_vertices, num_sets, sets, problem_instance, args)
	#####################################################
	init_time = time()
	count = Dict(:latest_improvement => 1,
	  			 :first_improvement => false,
	 		     :warm_trial => 0,
	  		     :cold_trial => 1,
				 :total_iter => 0,
				 :print_time => init_time)
	# 所有冷启动轮次中的最优解，即最后输出的最优解
	lowest = Tour(Int64[], typemax(Int64))
	start_time = time_ns()
	# 预计算：setdist存储了3种2维数组：集合到节点最小距离、节点到集合最小距离、集合与节点之间最小有向距离
	setdist = set_vertex_dist(dist, num_sets, membership)
	# 为删除/插入启发式函数初始化（启发式名称、lambda、各个时期的概率权重、优化分数以及选取次数）
	# 各个时期概率权重初始化为1，并计算各个时期总权重，便于后续为各个时期概率抽取启发式函数
	powers = initialize_powers(param)

	# 冷启动ing
	while count[:cold_trial] <= param[:cold_trials]
		# 每次冷启动重新构建初始解
		best = initial_tour!(lowest, dist, sets, setdist, count[:cold_trial], param)
		phase = :early
		
		# 第一次冷启动，初始化各个插入/删除启发式函数的权重...
		if count[:cold_trial] == 1
			powers = initialize_powers(param)
		# 后续冷启动，根据先前各个插入/删除启发式函数优化效果更新权重...			
		else
			power_update!(powers, param)
		end

		# 迭代ing 
		# 迭代阶段分为 1. an initial descent 2. several warm restarts
		# 迭代时期分为 1. early 2. mid 3. late
		# 第二迭代阶段中热启动次数超出限制，则退出迭代
		while count[:warm_trial] <= param[:warm_trials]
			iter_count = 1
			# current存储当前解
			current = Tour(copy(best.tour), best.cost)
			# temperature为当前温度（模拟退火接受新解概率的相关参数，temperature越高，越容易接受新解）
			# 论文5.3 Acceptance Criteria(i): Tem_init = p1%*w(T_best)/ln(2)
			temperature = 1.442 * param[:accept_percentage] * best.cost
			# temperature冷却系数
			cooling_rate = ((0.0005 * lowest.cost)/(param[:accept_percentage] * current.cost))^(1/param[:num_iterations])

			# 如果进入第二阶段，进入late时期，降低温度
			if count[:warm_trial]  > 0	  # if warm restart, then use lower temperature
		        temperature *= cooling_rate^(param[:num_iterations]/2)
				phase = :late
			end

			# 如果在迭代过程中存在first_improvement，则那么可以增加循环上限次数
			while count[:latest_improvement] <= 
				(count[:first_improvement] ? param[:latest_improvement] : param[:first_improvement])
				
				# 如果iter_count迭代次数超过一半，进入mid时期
				if iter_count > param[:num_iterations]/2 && phase == :early
					phase = :mid  # move to mid phase after half iterations
				end
				
				# 选择插入/删除启发式函数，删除插入N_r个节点，继续优化巡回路径，返回新解
				trial = remove_insert(current, best, dist, membership, setdist, sets, powers, param, phase)

		        # decide whether or not to accept trial
				# 两个接受新解的条件 1.根据预设参数设定概率 2.根据温度设置概率
				if accepttrial_noparam(trial.cost, current.cost, param[:prob_accept]) || accepttrial(trial.cost, current.cost, temperature)
					# 如果求解模式为“slow”，继续全部优化巡回
					param[:mode] == "slow" && opt_cycle!(current, dist, sets, membership, param, setdist, "full")
				    # 接受新解 如果trial.cost<原来current.cost，一定接受trial
					current = trial
		        end
				# 如果新解小于当前最优解
		        if current.cost < best.cost
					# 距离上次更新优化的次数重置为1
					count[:latest_improvement] = 1
					# 标记已有first_improvement
					count[:first_improvement] = true
					# 重置热启动（第一次冷启动没有该功能）
					if count[:cold_trial] > 1 && count[:warm_trial] > 1
						count[:warm_trial] = 1
					end
					# 继续全部优化巡回
					opt_cycle!(current, dist, sets, membership, param, setdist, "full")
					# 更新最优解
					best = current
	        	else
					# 反之距离上次优化的次数增1
					count[:latest_improvement] += 1
				end

				# 论文5.3 Alternate Stopping Critera 1. time is reached 2. lb cost is met
			    if best.cost <= param[:budget] || time() - init_time > param[:max_time]
					param[:timeout] = (time() - init_time > param[:max_time])
					param[:budget_met] = (best.cost <= param[:budget])
					timer = (time_ns() - start_time)/1.0e9
					lowest.cost > best.cost && (lowest = best)
					print_best(count, param, best, lowest, init_time)
					print_summary(lowest, timer, membership, param)
					return
				end

		        temperature *= cooling_rate
				iter_count += 1
				count[:total_iter] += 1
				print_best(count, param, best, lowest, init_time)
			end
			print_warm_trial(count, param, best, iter_count)
			# 每次冷启动初始an initial descent执行完毕，开启热启动
			# 每次热启动执行完毕，重置相关参数继续热启动
			count[:warm_trial] += 1
			count[:latest_improvement] = 1
			count[:first_improvement] = false
		end
		# 准备下一个冷启动
		lowest.cost > best.cost && (lowest = best)
		count[:warm_trial] = 0
		count[:cold_trial] += 1

		# print_powers(powers)

	end
	timer = (time_ns() - start_time)/1.0e9
	print_summary(lowest, timer, membership, param)
end
end
