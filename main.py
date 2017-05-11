#

import sympy.abc
from sympy.logic.boolalg import Not, And, Or
from sympy import Symbol
from sympy.logic.inference import satisfiable
from sympy.logic.boolalg import to_cnf
import mpmath
from itertools import product
#import pprint 


class Rule(object):
	def __init__(self, _name, _item, _body, _head):
		self.name = _name
		self.item = _item
		self.body = _body
		self.head = _head
	
		self.bodyExtension = []
		self.headExtension = []
		self.headWorlds = []
		#self.vw = set()
		#self.fw = set()
		#self.nw = set()
		self.dominates = set()

class World(object):
	def __init__ (self, _name, _state):
		self.name = _name
		self.state = _state
		self.F = set()
		self.dom = set()

	def print_worlds(self):
		for model in self.vw:
			print("%s is verified by: \n" % (self.item))
		for model in self.vw:	
			for key in model:
				print("Here we go: %s: %s \n" % (key, model[key]))
		for key in self.vw:
			print("key: %s, value: %s \n" % (key, self.vw[key]))
		print(" \n %s is violated by: \n" % (self.item))
		for model in self.fw:
			print(model)
		print("\n %s is netural with respect to: \n" % (self.item))
		for model in self.nw:
			print(model)

def compareDict(a, b):
	Ka = set(a.keys())
	Kb = set(b.keys())
	Ba = set(a.values())
	Bb = set(b.values())
	V = (Ka == Kb) & (Ba == Bb)


print("__________________________________________________________________________\n")
print("Welcome to the Naive Preferences Solver\n")
print("___________________________________________________________________________\n")
file_name = input("Please input the name of a text-file containing a set of rules (include the 'txt' extension) \n")
print("Name of file: %s \n" % (file_name))

file = open(file_name, "r+")

st = file.read()
print(st)

propositions_char = set()

for char in st:
	if(char.isalpha()):
		propositions_char.add(char)


for item in propositions_char:
	print(item)

propositions = set()
for item in propositions_char:
	new = Symbol(item)
	propositions.add(new)

print("Propositions: %s \n" % (propositions))


lines = [line.rstrip("\n") for line in open(file_name)]
#lines = [line.lstrip("(") for line in lines]
#lines = [line.rstrip(")") for line in lines]
temp1 = [line[1:] for line in lines]
temp2 = [line[:-1] for line in temp1]
temp3 = [line.split(",") for line in temp2]
dummy = []

rules = []
count = 0
for line in temp3:
	item = line[0] + "," + line[1]
	name = "r" + str(count)
	new = Rule(name, item, line[0], line[1])
	rules.append(new)
	count += 1

for i in rules:
	print("%s: %s \n" %(i.name, i.item))


num_worlds = list(range(2**len(propositions)))
world_names = ["w" + str(i) for i in num_worlds]

n = len(propositions)
table = list(product([False, True], repeat=n))
worlds = set()
count = 0
for row in table:
	state = dict(zip(propositions, row))
	new = World(world_names[count], state)
	worlds.add(new)
	#print(world)
	#worlds[world_names[count]] = state
	count +=1


#pprint.pprint(table)

print("Worlds")
for world in worlds:
	print("%s: %s \n" % (world.name, world.state))
for rule in rules:

	th1 = set()
	for char in str(rule.head):
		if(char.isalpha()):
			add = Symbol(char)
			th1.add(add)
	#th2 = propositions - th1
	th2 = propositions.difference(th1)
	#print("th2: %s, th1: %s\n" % (th2, th1))
	item = ""
	for p in th2:
		item +=  "&" + "(" +str(p) + "|" +  "~" +  str(p) + ")"
		#item += str(p) + "|" + " ~" + str(p)
	#item = item[:-1]
	head_check = rule.head + item
	#print("Head check: " + head_check + "\n")

	h_temp = satisfiable((head_check), all_models = True)
	for model in h_temp:
		new = {}	
		for key in model:
			new[key] = model[key]
		rule.headExtension.append(new)

	tb1 = set()
	for char in str(rule.body):
		if(char.isalpha()):
			add = Symbol(char)
			tb1.add(add)
	#th2 = propositions - th1
	tb2 = propositions.difference(tb1)
	#print("th2: %s, th1: %s\n" % (tb2, tb1))
	item = ""
	for p in tb2:
		item +=  "&" + "(" +str(p) + "|" +  "~" +  str(p) + ")"
		#item += str(p) + "|" + " ~" + str(p)
	#item = item[:-1]
	body_check = rule.body + item
	#print("Body check: " + body_check + "\n")

	b_temp = satisfiable((body_check), all_models = True)
	for model in b_temp:
		new = {}	
		for key in model:
			new[key] = model[key]
		rule.bodyExtension.append(new)




for rule in rules:
	print(" %s is satisified by \n" % (rule.head))
	print(len(rule.headExtension))
	for e in rule.headExtension:
		print(e)
	print(" %s is satisified by \n" % (rule.body))
	for e in rule.bodyExtension:
		print(e)

'''for world in worlds:
	print(world.name)
	for rule in rules:
		if(world.state in rule.bodyExtension):
			print("Yes\n")
		else:
			print("No\n")
	for rule in rules:
		if(world.state in rule.headExtension):
			print("Yes\n")
		else:
			print("No\n")'''

	#rule.Vhead = satisfiable((rule.head), all_models = True)
	
	#nbody = "~" + rule.head
	#rule.Nhead = satisfiable((nbody), all_models = True)

	#check_false = "~" + rule.head + " & " + rule.body
	#print("check_false: %s \n" % check_false)
	#rule.fw = satisfiable((check_false), all_models = True)
	


#for rule in rules:
#	rule.print_worlds()

for world in worlds:
	for r1 in rules:
		for r2 in rules:
			if world.state in r1.bodyExtension:
				print("%s body in %s \n" % (r1.name, world.name))
			if world.state in r2.bodyExtension:
				print("%s body in %s \n" % (r2.name, world.name))

			if(world.state not in r1.bodyExtension or world.state in r2.bodyExtension):
				if(world.state not in r1.headExtension or world.state not in r2.headExtension):
					if(world.state in r2.bodyExtension and world.state not in r1.bodyExtension):
						new = (r1.name, r2.name)
						world.dom.add(new)



for world in worlds:
	for d in world.dom:
		#for p in d:
		print("%s in world %s \n" % (d, world.name))


count = 0
for i in rules:
	print("%s: %s \n" % (count, i.body))
	count += 1


#for i in rules:
#	for j in rules:



'''K = a.keys() == b.keys()
#print(K)
#V = a.values() == b.values()
#print(V)


#print("Return Value : %s" %  cmp(a, b))


#print(line[2])	

p = "((P & ~Q), (R | ~P))"

q = p.split(",")

print(q)

for i in q:
	print(i)
	i.lstrip('(')
	i.rstrip(')')
	i.rstrip(',')
	#p = satisfiable(i)
	#print(p)
	print(i)'''



'''r1 =(A | B)
r2 =  (C & (B | D))
r3 =  (A | (C & D))
r4 = (~D | C)

c1 = to_cnf(r1)
c2= to_cnf(r2)
c3= to_cnf(r3)
c4= to_cnf(r4)


print(" c1 is %s, c2 is %s, c3 is %s, c4 is
lines = [line.rstrip('\n') for line in openfile_name)]
total = (c1 & c2 & c3 & c4)

print(total)

s = satisfiable(total)
print(s)
com = (A | ~A)
for key, value in s.items():
	if(value == False):
		add = key
	else: 
		add = Not(key)
	com = (com & add)

print(com)

#
total = (total & com)  
print(total)


s2 = satisfiable(total)
print(s2)

models = satisfiable((A | B), all_models = True)

for model in models:
	print(model)'''

