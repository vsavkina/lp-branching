
import random
import re
import numpy as np
from docplex.mp.model import Model
from math import floor, ceil
from time import time

def sort_nodes(incidence_matrix, strategy = 'lf'):

    if strategy == 'lf': #largest first

        result = np.argsort(np.sum(incidence_matrix, axis=1))

    elif strategy == 'sl': #smallest last

        result = []

        local_incidence_m = np.copy(incidence_matrix)

        nodes_by_degree = list(sort_nodes(local_incidence_m))

        for _ in range(vertices):

            smallest_node = nodes_by_degree.pop(0)

            result.append(smallest_node)

            local_incidence_m[smallest_node] = np.full((vertices), 2)

            local_incidence_m[:,smallest_node] = np.full((vertices), 2)

            nodes_by_degree = list(sort_nodes(local_incidence_m))

    else: #random

        result = random.sample(range(vertices), vertices)

    return result


def lower_bound_heuristics(incidence_matrix, sorted_nodes):

    clique = []

    while len(sorted_nodes) != 0:

        best_vertex = sorted_nodes[-1]

        clique.append(best_vertex + 1) # нумерация здесь с 0, в файле - с 1

        sorted_nodes = sorted_nodes[incidence_matrix[best_vertex, sorted_nodes] == 1]

    return clique, len(clique)


def coloring_graph(incidence_matrix, num_of_vertices, sorted_nodes):

    """Раскрасим граф для более строгих ограничений"""

    groups = np.array([-1] * num_of_vertices) #цвета вершин (вершины расположены в лексикографическом порядке

    num_of_groups = -1

    for i in range(num_of_vertices-1,-1,-1):

        neighboring_colors = groups[incidence_matrix[sorted_nodes[i]] == 1]

        current_color = 0

        while current_color in neighboring_colors:

            current_color += 1

        groups[sorted_nodes[i]] = current_color

        if current_color > num_of_groups: num_of_groups = current_color

    grouped_by_color = {}

    for i, node in enumerate(groups):

        if node in grouped_by_color:

            grouped_by_color[node].append(i)

        else:
            grouped_by_color[node] = [i]

    return grouped_by_color.values()

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


def branch_n_bound():

    global model, lower_bound, best_solution,timeout

    if time() - starting_time > 7200:

        timeout = True

        return

    current_solution = get_solution()

    if current_solution == None or round_ub(current_solution.objective_value) <= lower_bound:

        return

    integers_only = True

    for item,value in current_solution.iter_var_values():

        if not isinteger(value):

            integers_only = False

            break

    if integers_only:

        lower_bound = round_ub(current_solution.objective_value)

        best_solution = current_solution

        return

    var = choose_variable_for_branching(current_solution)

    branch_order = [0,1] if current_solution.get_value(var) < 0.5 else [1,0]

    for i in branch_order:

        new_constraint = model.add_constraint(variables[var] == i)

        branch_n_bound()

        model.remove_constraint(new_constraint)

    return


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
    #model.print_information()

    return model.solve()

def check_clique(best_solution, incidence_m, lenofclique):

    lenofclique = int(lenofclique)

    if not isinstance(best_solution, list): #клика найдена методом ветвей и границ

        best_solution = [int(var[1:]) for var in best_solution.get_value_dict(variables, keep_zeros=False)]

    for i in range(lenofclique):

        for j in range(i+1, lenofclique):

            if incidence_m[best_solution[i]-1, best_solution[j]-1] == 0: #нумерация в клике с 1, в матрице - с 0

                return False

    return len(set(best_solution)) == lenofclique

eps = 10**(-6)

model = Model(name='max_clique')

variables =  {}

mypath = input() # ссылка на граф
#mypath = 'DIMACS_all_ascii/C125.9.clq'

vertices, num_of_edges, incidence_m = read_dimacs_graph(mypath)

#Сгенерируем независимые подмножества, которые будет использовать для создания более сильных ограничений
independent_sets, constrained_nodes = [], []
sorted_lf =  sort_nodes(incidence_m) #список узлов в порядке возрастания степени
independent_sets.extend(coloring_graph(incidence_m, vertices, sorted_lf))
independent_sets.extend(coloring_graph(incidence_m, vertices, sort_nodes(incidence_m,'sl')))
for _ in range(50): independent_sets.extend(coloring_graph(incidence_m, vertices,sort_nodes(incidence_m,'rnd')))
independent_sets.sort(key = np.shape, reverse=True)

best_solution, lower_bound = lower_bound_heuristics(incidence_m,sorted_lf)


for var in range(vertices):
    #динамически создадим переменные и запишем их в словарь variables

    varname = 'x{}'.format(var + 1)

    variables[varname] = model.continuous_var(name=varname)

    model.add_constraint(variables[varname] <= 1)

for ind_set in independent_sets:

    rng = len(ind_set)

    if rng < 2: break

    untracked_nodes = [ (ind_set[node1], ind_set[node2]) for node1 in range(rng) for node2 in range(node1+1, rng)
                        if (ind_set[node1], ind_set[node2]) not in constrained_nodes] #пары узлов, на которых еще не наложены ограничения

    if not untracked_nodes:continue #на все пары из списка уже есть более сильное ограничение

    model.add_constraint(sum((variables[ 'x' + str(node + 1) ] for node in ind_set)) <= 1)

    constrained_nodes.extend(untracked_nodes)

#добавляем остальные ограничения

for var in range(vertices):
    for var2 in range(var+1, vertices):
        vn1, vn2 = 'x{}'.format(var + 1), 'x{}'.format(var2 + 1)
        if incidence_m[var, var2] == 0 and (var, var2) not in constrained_nodes:
            model.add_constraint(variables[vn1] +  variables[vn2] <= 1)


timeout = False

starting_time = time()

best_solution = None

branch_n_bound()

time_taken = time() - starting_time

assert check_clique(best_solution, incidence_m, lower_bound)

