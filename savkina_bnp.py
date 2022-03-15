import random
import re
import numpy as np
from docplex.mp.model import Model
from math import floor, ceil, inf
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

def set_exists(ind_set):

    for iset in independent_sets:

        if iset.issuperset(ind_set):
            return True

    return False


def round_bound(ov, bound = 'u'):
    if bound == 'u':
        round1, round2 = ceil, floor
    else:
        round1, round2 = floor,ceil
    ub_r = round1(ov)
    if bound =='u' and ov + eps >= ub_r or bound =='l' and ov + eps <= ub_r:
        return ub_r
    return round2(ov)

def choose_variable_for_branching(current_solution):

    all_values = current_solution.get_value_dict(variables, keep_zeros=False)

    def get_key(key,dict = all_values):
        """Ветвимся по переменной, которая ближе к целому значению"""
        return abs(dict[key] - 0.5)

    for key in sorted(all_values, key=get_key, reverse=True):
        if not isinteger(all_values[key]): return key

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

def get_solution(model, variables, goal = 'min'):

    if goal == 'min':

        model.minimize(sum(variables.values()))
    else:

        model.maximize(sum(variables.values()))

    return model.solve()


def maximize_set(ind_set, current_solution, graph_reversed = False):

    while current_solution:

        x_j = current_solution.pop(0)

        check_criteria = [incidence_m[get_var(x_i), get_var(x_j)] for x_i in ind_set]

        if (not graph_reversed and sum(check_criteria) == 0) or (graph_reversed and sum(check_criteria) == len(check_criteria)):
            ind_set.append(x_j)
            current_solution = non_neighbors([get_var(x_j)], current_solution)

    return frozenset(ind_set)


def sort_nodes_for_indsets(list_to_sort):

    return sorted(list_to_sort, key=lambda var: sum(incidence_m[get_var(var), :]))


non_neighbors = lambda iterable, all_vars: [node for node in all_vars
                                            if sum(incidence_m[get_var(node), iterable]) == 0]

var_to_int = lambda strvar: int(strvar[1:])   # для переменной 'xi' возвращает индекс в матрице инцидентности i

get_var = lambda variable: var_to_int(variable) if isinstance(variable, str) else variable

def column_generation(forbidden,exact = False):

    if not exact:

        current_solution = sorted(range(vertices), key = lambda i: model.dual_values(constraints_for_nodes)[i] / (sum(incidence_m[i,:]) + eps), reverse = True)
        while current_solution:

            ind_set = [current_solution.pop(0)]

            ind_set = maximize_set(ind_set, non_neighbors([get_var(ind_set[0])], current_solution))

            curr_set_sum = sum([variables['x%s' % x].solution_value for x in ind_set])
            set_not_in_sets = True

            if not set_exists(ind_set) and curr_set_sum - eps > 1 and ind_set not in forbidden:
                independent_sets.append(ind_set)
                return ind_set, inf
    else:
        dual_v = [dv if dv - eps > 0 else dv + eps for dv in model.dual_values(constraints_for_nodes) ]

        vertices_v = list(variables_slave.values())

        model_slave.remove_objective()

        model_slave.maximize(sum([dual_v[i] * vertices_v[i] for i in range(vertices)]))

        solution = model_slave.solve()
        if not solution: return None, None
        total_weight = sum([weight for weight,node in zip(dual_v, solution.get_all_values()) if node != 0])

        if total_weight >= 1.1:

            UB = model_slave.solution.get_objective_value()

            ind_set = {get_var(var) for var in variables_slave if variables_slave[var].solution_value == 1}

            assert ind_set not in forbidden

            if set_exists(ind_set): return None, None

            independent_sets.append(ind_set)

            return ind_set, UB

    return None, None

def add_variables_from_constraint(col):

    varname = 'x{}'.format(len(variables))

    variables[varname] = model.continuous_var(name=varname)

    for constraint_id in col:

        constr = constraints_for_nodes[constraint_id]
        model.remove_constraint(constr)
        constr.left_expr.add(variables[varname])
        model.add_constraint(constr)
        constraints_for_nodes[constraint_id] = constr


def column_generation_loop(forbidden, exact):

    col, ub = column_generation(forbidden, exact)

    ov_before_constraints = model.solution.get_objective_value()

    while col:

        lower_bound = round_bound(model.solution.get_objective_value()/ ub, 'l')

        if lower_bound >= f_best:

            return True

        add_variables_from_constraint(col)

        solution = get_solution(model, variables)

        if random.random() < 0.05:

            if abs(solution.get_objective_value() - ov_before_constraints) < 1e-3:

                return False

        if solution == None: break

        col, ub = column_generation(forbidden, exact)

    return False

def branch_n_price(forbidden = []):

    global f_best, best_solution, timeout

    if time() - starting_time > 1800:

        timeout = True
        return

    solution = get_solution(model, variables)

    if solution == None:

        return

    current_ov = round_bound(solution.get_objective_value(), 'l')

    for exact in (False, True):

        can_prune = column_generation_loop(forbidden, exact)
        if can_prune:
            return

    i = choose_variable_for_branching(solution)

    if not i:

        if current_ov < f_best:

            f_best = current_ov
            best_solution = solution

        return

    branch_order = [0, 1] if solution.get_value(i) < 0.5 else [1, 0]

    for constr in branch_order:

        if constr == 0:

            current_branch = model.add_constraint(-variables[i] >= 0)
            forb_set = independent_sets[get_var(i)]
            forbidden.append(forb_set)
            forb_set_for_sm = model_slave.add_constraint(sum([variables_slave['y%s' % index] for index in forb_set]) <= len(independent_sets[get_var(i)]) - 1)
        else:
            current_branch = model.add_constraint(variables[i] >= 1)

        branch_n_price(forbidden)

        model.remove_constraint(current_branch)

        if constr == 0:

            forb_set = forbidden.pop(-1)
            model_slave.remove_constraint(forb_set_for_sm)






model = Model(name='vcp')
model_slave = Model(name = 'violated_c')


eps = 1e-6

variables =  {}
variables_slave = {}

mypath = input() # ссылка на граф
#mypath = 'VCP/myciel4.col'


vertices, num_of_edges, incidence_m = read_dimacs_graph(mypath)

#Сгенерируем независимые подмножества
independent_sets = []
sorted_lf =  sort_nodes(incidence_m) #список узлов в порядке возрастания степени
independent_sets.extend(coloring_graph(incidence_m, vertices, sorted_lf))
f_best = len(independent_sets) #начальная upper bound для модели
independent_sets.extend(coloring_graph(incidence_m, vertices, sort_nodes(incidence_m,'sl')))
for _ in range(50): independent_sets.extend(coloring_graph(incidence_m, vertices,sort_nodes(incidence_m,'rnd')))
independent_sets.sort(key = np.shape, reverse=True)


independent_sets = set([maximize_set(ind_set, [i for i in range(vertices) if i not in ind_set]) for ind_set in independent_sets])
independent_sets = list(independent_sets)


for var in range(len(independent_sets)):

    varname = 'x{}'.format(var)

    variables[varname] = model.continuous_var(name=varname)

for node in range(vertices):

    varname = 'y%s' % node

    variables_slave[varname] =  model_slave.integer_var(name=varname)

    model.add_constraint(sum([variables['x%s' % no] for no in range(len(independent_sets)) if node in independent_sets[no]]) >= 1)

constraints_for_nodes = [c for c in model.iter_constraints()]

for var in variables_slave:
    for var2 in variables_slave:
        if incidence_m[get_var(var), get_var(var2)] == 1:
            model_slave.add_constraint(variables_slave[var] + variables_slave[var2] <= 1)

starting_time = time()
timeout = False
best_solution = None
branch_n_price()

time_taken = time() - starting_time
print(f_best, best_solution)
