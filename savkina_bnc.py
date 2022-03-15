
import random
import re
import numpy as np
from docplex.mp.model import Model
from math import floor, ceil
from time import time
from docplex.mp.constr import LinearConstraint

def sort_nodes(incidence_matrix, strategy = 'lf'):

    if strategy == 'lf': #largest first

        result = np.argsort(np.sum(incidence_matrix, axis=1))

    else: #random

        result = random.sample(range(vertices), vertices)

    return result


def lower_bound_heuristics(incidence_matrix, sorted_nodes):

    clique = []

    while len(sorted_nodes) != 0:

        best_vertex = sorted_nodes[random.randrange(-1,max(-len(sorted_nodes)-1, -4),-1)]

        clique.append(best_vertex + 1) # нумерация здесь с 0, в файле - с 1

        sorted_nodes = sorted_nodes[incidence_matrix[best_vertex, sorted_nodes] == 1]

    return clique, len(clique)

def isinteger(value):
    if value - eps <= floor(value) or value + eps >= ceil(value):
        return True
    return False

def round_ub(upper_bound):
    ub_ceil = ceil(upper_bound)
    if upper_bound + eps >= ub_ceil:
        return ub_ceil
    return floor(upper_bound)

def choose_variable_for_branching(current_solution):

    all_values = current_solution.get_value_dict(variables, keep_zeros=False)

    def get_key(key,dict = all_values):
        """Ветвимся по переменной, которая ближе к целому значению"""
        return abs(dict[key] - 0.5)

    for key in sorted(all_values, key=get_key, reverse=True):
        if all_values[key] + eps < 1 and all_values[key] - eps > 0: return key


def branch_n_cut():

    global model, lower_bound, best_solution,timeout

    if time() - starting_time > 7200:

        timeout = True

        return

    current_solution = get_solution()

    if current_solution == None or round_ub(current_solution.objective_value) <= lower_bound:

        return

    if random.random() < 0.01: # на каждом ~100м вызове bnc удаляем лишние ограничения

        for constraint in model.iter_constraints():
            if constraint.slack_value - eps > 0:
                try:
                    iterator = constraint.iter_variables()
                    next(iterator), next(iterator) #проверяем количество переменных в ограничении
                    model.remove_constraint(constraint)
                except StopIteration:
                    continue

    sep = separation(current_solution, model)
    ov = current_solution.objective_value # objective value до отсечения

    while sep:

        model.add_constraint(sum((variables[node] for node in sep)) <= 1)

        current_solution = get_solution()

        if current_solution == None or round_ub(current_solution.objective_value) <= lower_bound:
            return

        if random.random() < 0.01 and ov - current_solution.objective_value < 1e-3:
            #примерно на каждой 100-й итерации проверяем, как меняется целевая ф-я
            break

        sep = separation(current_solution, model)

    integers_only = True

    for item,value in current_solution.iter_var_values():

        if not isinteger(value):

            integers_only = False

            break

    if integers_only:

        violated_c = check_clique(current_solution, incidence_m, round_ub(current_solution.objective_value))

        if not violated_c:

            lower_bound = round_ub(current_solution.objective_value)

            best_solution = current_solution

            return

        for constraint in violated_c:

            sorted_nodes = sort_nodes_for_indsets()

            model.add_constraint(sum((variables[node] for node in maximize_set(constraint,
                                    non_neighbors([var_to_int(c) for c in constraint], sorted_nodes)))) <= 1)

        branch_n_cut()

        return

    var = choose_variable_for_branching(current_solution)

    branch_order = [0,1] if current_solution.get_value(var) < 0.5 else [1,0]

    for i in branch_order:

        new_constraint = model.add_constraint(variables[var] == i)

        branch_n_cut()

        model.remove_constraint(new_constraint)

    return


def maximize_set(ind_set, current_solution):

    while current_solution:

        x_j = current_solution.pop(0)

        if sum([incidence_m[var_to_int(x_i), var_to_int(x_j)] for x_i in ind_set]) == 0:

            ind_set.append(x_j)

            current_solution = non_neighbors([var_to_int(x_j)], current_solution)

    return ind_set

def sort_nodes_for_indsets():

    """ Упорядочивает вершины по значению параметра var_value/degree """

    return sorted(variables, key=lambda var: variables[var].solution_value / sum(incidence_m[var_to_int(var) , :]),
           reverse=True)


non_neighbors = lambda iterable, all_vars: [node for node in all_vars
                                            if sum(incidence_m[var_to_int(node) , iterable]) == 0]

var_to_int = lambda strvar: int(strvar[1:]) - 1 #для переменной 'xi' возвращает индекс в матрице инцидентности (i-1)

def separation(solution, model):

    current_solution = sort_nodes_for_indsets()

    while current_solution:

        ind_set = [current_solution.pop(0)]

        ind_set = maximize_set(ind_set, non_neighbors([var_to_int(ind_set[0])], current_solution))

        curr_set_sum = sum([variables[x].solution_value for x in ind_set])

        if curr_set_sum - eps > 1:

            return ind_set
    

def read_dimacs_graph(path_to):

    with open(path_to, 'r') as f:

        for line in f:

            if line.startswith('p'):

                vertices, num_of_edges = map(int, re.findall('\d+',line)[:2])

                incidence_m = np.zeros((vertices, vertices))

            elif line.startswith('e'):

                _, v1, v2 = line.split()

                v1, v2 = int(v1)-1, int(v2)-1

                incidence_m[v1, v2] = 1

                incidence_m[v2, v1] = 1

    return (vertices, num_of_edges, incidence_m)

def get_solution():

    global model, variables

    model.maximize(sum(variables.values()))
    return model.solve()

    #model.print_information()

def check_clique(best_solution, incidence_m, lenofclique):

    violated_constraints = []

    if not isinstance(best_solution, list): #клика найдена методом ветвей и границ

        best_solution = [int(var[1:]) for var in best_solution.get_value_dict(variables, keep_zeros=False)]

    for i in range(lenofclique):

        for j in range(i+1, lenofclique):

            if incidence_m[best_solution[i]-1, best_solution[j]-1] == 0: #нумерация в клике с 1, в матрице - с 0

                violated_constraints.append(['x%s' % best_solution[i], 'x%s' % best_solution[j]])

    return violated_constraints

eps = 10**(-6)

model = Model(name='max_clique')

variables =  {}

mypath = input() # ссылка на граф

vertices, num_of_edges, incidence_m = read_dimacs_graph(mypath)

best_solution, lower_bound = lower_bound_heuristics(incidence_m,sorted_lf)

for _ in range(3000):
    tmp_solution, tmp_lb = lower_bound_heuristics(incidence_m,sorted_lf)
    if tmp_lb > lower_bound:
        best_solution, lower_bound = tmp_solution, tmp_lb


for var in range(vertices):
    #создадим переменные и запишем их в словарь variables

    varname = 'x{}'.format(var + 1)

    variables[varname] = model.continuous_var(name=varname)

    model.add_constraint(variables[varname] <= 1)


timeout = False

starting_time = time()

branch_n_cut()

time_taken = time() - starting_time