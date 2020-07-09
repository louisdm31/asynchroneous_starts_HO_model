import random

n = 10
l = 50
test = 20000


init = [0,1,0,0]

graph = [
    [1,1,0,1],
    [1,1,0,0],
    [1,0,1,0],
    [1,0,0,1],
]
def test_sync(init, graph, n):
	def min_i(init, graph, i, n):
		min_ho = n
		for j in range(len(init)):
			if graph[j][i] == 1:
				min_ho = min(init[j], min_ho)
		return min_ho
		

	graph_ = graph(len(init), n)
	#print(graph_)
	for w in range(100):
		#print(init)
		if verif_sync(init):
			return init, graph_, w
		init = [(k+1)%(n+1) for k in init]
		init = list(map(lambda x:min_i(init, graph_, x, n), range(len(init))))

	return init, graph_, -1

def rand_list(l, n, md = 0):
	if md == 0:
		return list(map(lambda x:random.randint(0,n), range(l)))
	else:
		return list(map(lambda x:random.randint(0,n) // md, range(l)))

def graph_semi_complet(l):
	graph = list(map(lambda x:rand_list(l, 4, 4), range(l)))
	for i in range(l):
		for j in range(i):
			graph[j][i] = 1 - graph[i][j]
		graph[i][i] = 1
	return graph

def graph_strong_connect(l, n):
	graph = list(map(lambda x:rand_list(l, 4, 4), range(l)))
	for i in range(1, l):
		graph[i][random.randint(0, i-1)] = 1
		graph[random.randint(0, i-1)][i] = 1
		graph[i][i] = 1
	return graph

def graph_strong_connect_star(l, n):
	graph = list(map(lambda x:rand_list(l, 4, 4), range(l)))
	graph[0] = [1 for w in range(l)]
	for i in range(1, l):
		graph[i][random.randint(0, i-1)] = 1
		graph[i][i] = 1
	return graph

def serie_etoile(l):
	global n
	init = rand_list(l, n)
	graph = list(map(lambda x:rand_list(l, 1), range(l)))
	for i in range(l):
		for j in range(i):
			graph[j][i] = 1 - graph[i][j]
		graph[i][i] = 1
	return test_sync(init, graph), init, graph

def verif_sync(fin):
	for h in range(1,l):
		if fin[h] != fin[0]:
			return False
	return True

def test_serie(l, n):
	distr = [0]*20
	for w in range(test):
		init = rand_list(l, n)
		fin, graph, r = test_sync(init, graph_strong_connect_star, n)
		if r == -1:
			print(init, graph)
			break
		else:
			distr[r] += 1
	print(' - '.join(map(str, distr)))

#print(test_sync(init, lambda x, s:graph, n))
test_serie(l, n)
