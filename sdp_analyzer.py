# Script performing the rounding process.

import scipy
import numpy
import numpy.linalg
import math

S = 6  # S could be 4,5,6. Current dir must contain files words<S>.dat-s and words<S>.out where <S> is  4,5,6.

D = 1000000  # Denominator of rational certificate.

num_constraints = 0
num_blocks = 0
total_variables = 0
block_sizes = []
M = 0


def get_index(block_num, row, column):
    index = 1
    for i in range(block_num - 1):
        size = block_sizes[i]
        index += size * (size + 1) / 2
    size = block_sizes[block_num - 1]
    if block_num == num_blocks:
        index += row - 1
    else:
        column = column - row
        while row > 1:
            index += size
            size -= 1
            row -= 1
        index += column
    return int(index)


def read_problem_file():
    f = open("words" + str(S) + ".dat-s", 'r')
    line = f.readline().strip()
    global num_constraints
    num_constraints = int(line)
    line = f.readline().strip()
    global num_blocks
    num_blocks = int(line)
    parts = f.readline().split()
    for part in parts:
        block_sizes.append(abs(int(part)))
    parts = f.readline().split()
    constants = numpy.zeros([num_constraints], float)
    global M
    for i in range(num_constraints):
        constants[i] = parts[i]
        if constants[i] > M:
            M = int(constants[i])
    global total_variables
    total_variables = 0
    for block_num in range(num_blocks-1):
        total_variables += block_sizes[block_num] * (block_sizes[block_num] + 1) / 2
    total_variables += num_constraints+1
    total_variables = int(total_variables)
    matrix = scipy.sparse.dok_matrix((num_constraints, total_variables), dtype='d')
    while True:
        line = f.readline()
        if len(line) == 0:
            break
        parts = line.split()
        if len(parts) == 0:
            continue
        constraint = int(parts[0])
        block_num = int(parts[1])
        row = int(parts[2])
        column = int(parts[3])
        value = int(parts[4])
        index = get_index(block_num, row, column)
        if row != column:
            value = 2 * value
        if constraint > 0:
            matrix[constraint - 1, index - 1] += value
    f.close()
    matrix = matrix.tocsc()
    return matrix, constants


def read_solution_file():
    f = open("words" + str(S) + ".out", 'r')
    f.readline()
    primal = []
    for block_num in range(num_blocks-1):
        primal.append(numpy.zeros([block_sizes[block_num], block_sizes[block_num]], float))
    primal.append(numpy.zeros([1, num_constraints+1], float))
    while True:
        line = f.readline()
        if len(line) == 0:
            break
        parts = line.split()
        if len(parts) == 0 or int(parts[0]) != 2:
            continue
        block_num = int(parts[1])
        row = int(parts[2])
        column = int(parts[3])
        value = float(parts[4])
        block = primal[block_num - 1]
        if block_num == num_blocks:
            block[0, column - 1] += value
        else:
            block[row - 1, column - 1] += value
        if row != column:
            block[column - 1, row - 1] += value
    return primal


def write_certificate(f, lt, block_num):
    f.write("Block " + str(block_num+1) + " of L (dimension "+str(block_sizes[block_num])+")\n")
    for i in range(block_sizes[block_num]):
        for j in range(i+1):
            f.write(str(int(lt[i, j]))+" ")
        f.write("\n")


def compute_certificate(sol):
    min_diagonal_l = None
    m_spread = numpy.zeros([total_variables], float)
    f = open("words" + str(S) + ".cert", 'w')
    for block_num in range(num_blocks-1):
        lower = scipy.linalg.cholesky(sol[block_num], lower=True)
        lower *= D
        lower = lower.round()
        write_certificate(f, lower, block_num)
        mini = lower[0, 0]
        for i in range(1, block_sizes[block_num]):
            if lower[i, i] < mini:
                mini = lower[i, i]
        if min_diagonal_l is None or mini < min_diagonal_l:
            min_diagonal_l = mini
        m = numpy.matmul(lower, lower.T)
        for i in range(block_sizes[block_num]):
            for j in range(i, block_sizes[block_num]):
                index = get_index(block_num+1, i+1, j+1)
                m_spread[index-1] += m[i, j]
    f.write("Slack block of L (diagonal of order " + str(num_constraints+1) + ")\n")
    for i in range(num_constraints+1):
        lower = math.sqrt(sol[num_blocks-1][0, i])
        lower = int(lower * D)
        f.write(str(lower)+"\n")
        if lower < min_diagonal_l:
            min_diagonal_l = lower
        m = lower*lower
        index = get_index(num_blocks, i + 1, i + 1)
        m_spread[index - 1] += m
    f.close()
    return m_spread, int(min_diagonal_l)


a, const = read_problem_file()
print("Number of constraints:", num_constraints)
print("Number of variables:", total_variables)
print("Number of blocks (including slack block):", num_blocks)
p = read_solution_file()
print("Original SDP result:", p[num_blocks-1][0, 0])
rational_spread, min_diagonal_lower = compute_certificate(p)
print("Lowest diagonal element in L:", min_diagonal_lower)
err = a.dot(rational_spread) - const * D * D
inf_norm = max(abs(err.min(initial=None)), err.max(initial=None))
print("Epsilon:", int(inf_norm), "/", D*D, "=", inf_norm/(D*D))
res = rational_spread[get_index(num_blocks, 1, 1)-1]
print("Rounded SDP result:", int(res), "/", D*D, "=", res/(D*D))
print("Rounded SDP result minus epsilon:", int(res-inf_norm), "/", D*D, "=", (res-inf_norm)/(D*D))
print("Final result divided by M="+str(M)+":", str((res-inf_norm)/(D*D*M))[0:6]+"...")
