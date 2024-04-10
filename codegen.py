import sys
import re
text = "ex1 x,y,z: af all1 u,v : & ex2 a : b"
#result = re.findall(r"ex1[^:]*:", text)

#turns prefix x,y,z: to prefix x,y,z where x appendage, y appendage .. :
def add_where(string, prefix):
	start = len(prefix)
	s0 = string[start:-1] # ex1(-stuff-): -> (-stuff-) 
	return string[:-1] + " where "+ " & ".join( map( lambda x: "$U"+prefix[-1] +"("+ x + ") ", s0.split(",") ) ) +":" # x,y,z -> x in V, y in V, z in V

def replace_quantifiers(s):
	for pre in ["ex1","ex2","all1","all2"]:
		result = re.findall(pre+"[^:]*:", s)
		for l0 in result:
			s = s.replace(l0,add_where(l0,pre))
	return re.sub(' +', ' ',s)

#print(replace_quantifiers(text))

k =int(sys.argv[1])

fl = open("temp.mona",'r')

make_graph = fl.read()
fl.close() 
"""
m2l-tree;
#setup
var2 dummy;
var2 fusion;
"""

#setup
setup = """m2l-tree;
#setup
var2 fusion;
#var2 dummy;

"""

#generators for 0..k, (0,0),..(k,k) 
r = [(i,) for i in range(k)]
r2 = [(i,j) for i in range(k) for j in range(i+1,k)]
r2_ = [f for i in range(k) for j in range(k) for f in ( min (i,j) , max(i,j) ) if i !=j]

#takes an fstring and separator
def gen(string,sep,l): return sep.join( map(lambda x:string.format(*x), l) ) 
def genS(string,sep,l): return sep.join( map(lambda x:string.format(x), l) ) 


#defines each line using gen
n0 = "var2 n0;"
n1 = "var2 n1;"
n2 = "var2 n2;"
make_forgets = "var2 " + gen("forget{}",",",r) +";" #var2 forget0, forget1, forget2;
make_edges = "var2 " + gen("edge_{}_{}",",",r2) +";" #var2 edge_0_1, edge_0_2, edge_1_2;
make_vertices = "var2 " + gen("vertex_{}",",",r) +";" #var2 forget0, forget1, forget2;

#make unique 
xor_def = "pred xor(var0 x,y) = (x & (~y)) | ((~x) & y) ;"
sets = ["fusion"] + ["forget{0}".format(*i) for i in r] + ["edge_{0}_{1}".format(*i) for i in r2] + ["vertex_{0}".format(*i) for i in r]

l9 = []
l9_ = "(" +genS(" x in {}"," | ",sets)+")"
for i in range(len(sets)):
	l9.append( "(x in "+sets[i] + " & " +genS("x notin {}"," & ",(sets[:i] + sets[i+1:])) +")")
check_unique ="assert all1 x: (" + l9_ + ")& ("+ " |\n\t\t\t".join(l9) + ");"

#macro predicates
make_u1 ="\npred $U1(var1 x) = $U2({x});" 
make_universe_set = "pred $U2(var2 X) = X sub " + gen("forget{}", " union ", r) + ";" +make_u1
define_is_forget = "pred is_forget(var1 x) =  " + gen("x in forget{}"," | ",r) +";" ##pred forget(var1 x) = x in forget0 | x in forget1 | x in forget2;
define_is_edge = "pred is_edge(var1 x)   = " + gen("x in edge_{}_{}"," | ",r2) +";" ##pred is_tree_constant(var1 x) = x in edge_0_1 | x in edge_0_2 | x in edge_1_2;
define_is_vertex = "pred is_vertex(var1 x) = " + gen("x in vertex_{}", " | ",r) +";" ##pred is_tree_constant(var1 x) = x in vertex_0 | x in vertex_1 | x in vertex_2;
define_is_constant = "pred is_tree_constant(var1 x) = is_vertex(x) | is_edge(x);"




"""pred all_ports_forgot(var1 x) = ex1 y0,y1,y2:  
	(has_0(x) => y0 < x & y0 in forget0 ) &
	(has_1(x) => y1 < x & y0 in forget1 ) &
	(has_2(x) => y2 < x & y0 in forget2 ) ;

"""
forget_ports = """
pred all_ports_forgot(var1 x) = ( is_edge(x) => ex1 y1,y2: y1~=y2 & forgets(y1,x) & forgets(y2,x) ) &
				( is_vertex(x) => ex1 y: forgets(y,x) );
""" 

#ex1 " + gen("y{}",",",r) + ":" +gen("""
#	(has_{0}(x) => y{0} < x & y{0} in forget{0} ) ""","&",r) + ";"


"""
pred has_0(var1 x) = x in edge_0_1 | x in edge0_2 ;
pred has_1(var1 x) = x in edge_0_1 | x in edge1_2 ;
pred has_2(var1 x) = x in edge_0_2 | x in edge1_2 ;
"""
l5_ = "|".join([" x in edge_{{}}_{{}} "] * (k-1) )
define_edge_has_i = gen("pred has_{0}(var1 x) ="+l5_ +" | x in vertex_{0}", ";\n", r).format(*r2_) + ";"
"""
# forgets_i(v,e) if v forgets i in e
pred forgets0(var1 v, var1 e) = v < e & forget0(v) & has_0(e) & all1 x: (v<x & x<e) => ~forget0(x);
pred forgets1(var1 v, var1 e) = v < e & forget1(v) & has_1(e) & all1 x: (v<x & x<e) => ~forget1(x);
pred forgets2(var1 v, var1 e) = v < e & forget2(v) & has_2(e) & all1 x: (v<x & x<e) => ~forget2(x);
#
"""

define_forgets_i = gen("pred forgets{0}(var1 v, var1 e) = v < e & is_tree_constant(e) & v in forget{0} & has_{0}(e) & all1 x: (v<x & x<e) => x notin forget{0}",";\n",r)+";"
define_incident = "pred incident(var1 v, var1 e) = is_edge(e) & forgets(v,e);"

#pred incident(var1 v, var1 e) = incident0(v,e) | incident1(v,e) | incident2(v,e);

define_forgets = "pred forgets(var1 v, var1 e) ="+gen(" forgets{0}(v,e)"," |",r) + ";"

define_leaf = """
#free predicates
pred leaf(var1 x) = all1 y: (~x<y);
"""

define_domain = """
pred domain() = all1 x:# defined(x) &
			( leaf(x) <=> is_tree_constant(x) ) &
			( leaf(x) => all_ports_forgot(x) ) &
			( is_forget(x) => (all1 y: x.1 ~= y) )& 
			( is_forget(x) => ex1 y: forgets(x,y) )&
			( x in fusion => ex1 y0,y1: x.0 = y0 & x.1 = y1) ;
"""

#edge model
define_universe ="""
pred universe1(var1 x) = is_tree_constant(x);
pred universe2(var2 X) = all1 x where x in X: universe1(x);
"""
define_edge = """
pred edge(var1 u, var1 v) = ex1 e: u~= v & incident(u,e) & incident(v,e);
"""
rest = """ 
assert ex1 x,y: is_forget(x) & x<y;

assert domain();

""" + replace_quantifiers(sys.argv[2]) +";"
print("\n\n".join([setup] +[n0,make_forgets,n1,make_edges,n2,make_vertices] + [make_universe_set] + [make_graph] +[check_unique] + [define_is_forget,define_is_edge,define_is_vertex,define_is_constant] + [define_edge_has_i,define_forgets_i,define_forgets,define_incident,forget_ports] +[define_leaf,define_domain,define_universe,define_edge] +[rest]))
