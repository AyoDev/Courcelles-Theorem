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
#-------------code generation starts----------

"""
m2l-tree;
#setup
var2 dummy;
var2 fusion;
"""

#setup
setup = """m2l-tree;
#setup

"""

#generators for 0..k, (0,0),..(k,k) 
r = [(i,) for i in range(k)]
r2 = [(i,j) for i in range(k) for j in range(i+1,k)]
r2_ = [f for i in range(k) for j in range(k) for f in ( min (i,j) , max(i,j) ) if i !=j]

#takes an fstring and separator
def gen(string,sep,l): return sep.join( map(lambda x:string.format(*x), l) ) 
def genS(string,sep,l): return sep.join( map(lambda x:string.format(x), l) ) 


#defines each line using gen

#define bitsrting encoding
#00#000#000
#

#first 2 bits for type of vertex
# 00 -> forget, 11->fusion, 10 -> lone vertex 01-> lone edge
define_bits = """
var2 bit1;
var2 bit2;
pred is_fusion(var1 x) = x in bit1 & x in bit2;
pred is_forget(var1 x) = x notin bit1 & x notin bit2;
pred is_vertex(var1 x) = x in bit1 & x notin bit2;
pred is_edge(var1 x) = x notin bit1 & x in bit2;
pred is_tree_constant(var1 x) = is_edge(x) | is_vertex(x);
"""

#next bits encode numbers using binary to make th code more efficient
#
number_of_bits = len(bin(k)) -2 # number of bits needed
r0 = [(i,) for i in range(number_of_bits)]
define_num1_bits="var2 " + gen("num1_bit{}",", ",r0) +";"
define_num2_bits="var2 " + gen("num2_bit{}",", ",r0) +";"


#making sets for being a fusion/forgt ...
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
make_u1 ="\npred $U1(var1 x) = is_forget(x);" 
make_universe_set = "pred $U2(var2 X) = empty(X inter (bit1 union bit2));" +make_u1

#define_is_forget = "pred is_forget(var1 x) =  " + gen("x in forget{}"," | ",r) +";" ##pred forget(var1 x) = x in forget0 | x in forget1 | x in forget2;
#define_is_edge = "pred is_edge(var1 x)   = " + gen("x in edge_{}_{}"," | ",r2) +";" ##pred is_tree_constant(var1 x) = x in edge_0_1 | x in edge_0_2 | x in edge_1_2;
#define_is_vertex = "pred is_vertex(var1 x) = " + gen("x in vertex_{}", " | ",r) +";" ##pred is_tree_constant(var1 x) = x in vertex_0 | x in vertex_1 | x in vertex_2;
#define_is_constant = "pred is_tree_constant(var1 x) = is_vertex(x) | is_edge(x);"




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

# i want to check if 2 elements have the same number encoding
# forget nodes
# check
define_same1 = "pred same1(var1 x,y) = " + gen("(x in num1_bit{0} <=> y in num1_bit{0})"," & ",r0) + ";"
define_same2 = "pred same2(var1 x,y) = " + gen("(x in num1_bit{0} <=> y in num2_bit{0})"," & ",r0) + ";"
define_same  = "pred same(var1 x,y) = (( is_vertex(y) & same1(x,y) ) | (is_edge(y) & (same1(x,y) | same2(x,y) )));"
#

"""
pred has_0(var1 x) = x in edge_0_1 | x in edge0_2 ;
pred has_1(var1 x) = x in edge_0_1 | x in edge1_2 ;
pred has_2(var1 x) = x in edge_0_2 | x in edge1_2 ;
"""
l5_ = "|".join([" x in edge_{{}}_{{}} "] * (k-1) )
define_edge_has_i = gen("pred has_{0}(var1 x) ="+l5_ +" | x in vertex_{0}", ";\n", r).format(*r2_) + ";"
"""
# forgets_i(v,e) if v forgets i in e
pred forgets(var1 v, var1 e) = v < e & is_forget(v) & same(v,e) & all1 x: (v<x & x<e) => ~forget(x);
pred forgets1(var1 v, var1 e) = v < e & forget1(v) & has_1(e) & all1 x: (v<x & x<e) => ~forget1(x);
pred forgets2(var1 v, var1 e) = v < e & forget2(v) & has_2(e) & all1 x: (v<x & x<e) => ~forget2(x);
#
"""

#define_forgets_i = gen("pred forgets{0}(var1 v, var1 e) = v < e & is_tree_constant(e) & v in forget{0} & has_{0}(e) & all1 x: (v<x & x<e) => x notin forget{0}",";\n",r)+";"
define_incident = "pred incident(var1 v, var1 e) = is_edge(e) & forgets(v,e);"

#pred incident(var1 v, var1 e) = incident0(v,e) | incident1(v,e) | incident2(v,e);

define_forgets = "pred forgets(var1 v, var1 e) = v < e & is_forget(v) & same(v,e) & all1 x: (v<x & x<e & is_forget(x)) => ~same(x,v);"

define_leaf = """
#free predicates
pred leaf(var1 x) = all1 y: (~x<y);
"""

define_domain = """
pred defined(var1 x) = is_edge(x) => ~same2(x,x);

pred domain() = all1 x: defined(x) &
			( leaf(x) <=> is_tree_constant(x) ) &
			( leaf(x) => all_ports_forgot(x) ) &
			( is_forget(x) => (all1 y: x.1 ~= y) )& 
			( is_forget(x) => ex1 y: forgets(x,y) )&
			( is_fusion(x) => ex1 y0,y1: x.0 = y0 & x.1 = y1) ;
"""

#edge model
define_edge = """
pred edge(var1 u, var1 v) = ex1 e: u~= v & incident(u,e) & incident(v,e);
"""
rest = """ 
assert domain();

""" + replace_quantifiers(sys.argv[2]) +";"
print("\n\n".join([setup,define_bits] +[n0,define_num1_bits,n1,define_num2_bits] + [make_universe_set] + [make_graph] + [define_same1,define_same2,define_same] + [define_forgets,define_incident,forget_ports] +[define_leaf,define_domain,define_edge] +[rest]))
