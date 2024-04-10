import networkx as nx
import matplotlib.pyplot as plt
import sys

name = sys.argv[1]

G = nx.Graph()

data = open(name, "r")

lines = data.read().splitlines()
lines = [ x for x in lines if x[0] != "c"]
n = int(lines[0].split(" ")[2])
G.add_nodes_from(range(1,n+1))

for e in lines[1:] :
	e = e.split(" ")
	x = int(e[0])
	y = int(e[1])
	G.add_edge(x,y)

subax1 = plt.subplot(121)
nx.draw(G, with_labels=True, font_weight='bold')
#subax2 = plt.subplot(122)
#nx.draw_shell(G, nlist=[range(5, 10), range(5)], with_labels=True, font_weight='bold')
plt.show()
