#
#import sympy.abc
#from sympy.logic.boolalg import Not, And, Or
from sympy import Symbol
from sympy.logic.inference import satisfiable
#from sympy.logic.boolalg import to_cnf
from mpmath import*
#import mpmath
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
		self.setHeadExension = []
		self.setBodyExension = []

		self.headWorlds = []
		#self.vw = set()
		#self.fw = set()
		#self.nw = set()
		self.dominates = set()

class World(object):
	def __init__ (self, _name, _state):
		self.name = _name
		self.state = _state
		self.value = set()
		self.F = set()
		self.dom = set()




def obtain_atomic_formulas(file):
	propositions = set()
	for line in file:
		if line.startswith("("):
			prop_char = set()
			for char in line:
				#print(str(char))
				if(str(char).isalpha()):
					prop_char.add(str(char))
			for item in prop_char:
				new = Symbol(item)
				propositions.add(new)
	return propositions

def construct_rules_dict(file):
	lines = []
	for line in file:
		if line.startswith("("):
			lines.append(line.rstrip("\n"))
	#lines = [line.rstrip("\n") for line in file]
	temp1 = [line[1:] for line in lines]
	temp2 = [line[:-1] for line in temp1]
	temp3 = [line.split(",") for line in temp2]
	rules = {}
	count = 0
	for line in temp3:
		item = line[0] + "," + line[1]
		name = "r" + str(count)
		new = Rule(name, item, line[0], line[1])
		rules.update({name: new})
		#rules[name] = new
		count += 1
	return rules	

def construct_worlds(propositions):
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
		count +=1
	return worlds

def world_values(world):
	for world in worlds:
		value = set()
		for k, v in world.state.items():
			#print("Is this working? \n")
			#print("World K %s v %s \n" % (k, v))
			if(v == True):
				value.add(str(k))
			else:
				value.add("~" + str(k))

		world.value = value


#Key: A, model {A: True, D: False, C: False}
def assingn_rule_extensions(rules):
	for k, rule in rules.items():
		
		h_temp = satisfiable(rule.head, all_models = True)
		for model in h_temp:
			new = {}	
			for key in model:
				new[key] = model[key]
			rule.headExtension.append(new)
		

		b_temp = satisfiable(rule.body, all_models = True)
		for model in b_temp:
			new = {}	
			for key in model:
				new[key] = model[key]
			rule.bodyExtension.append(new)

def assign_sets_rules(rules):
	for k, rule in rules.items():
		h_small_worlds = []
		for item in rule.headExtension:
			_new = set()
			for key, value in item.items():
				#print("Key: %s, Value %s" % (key, value))
				if(value == True):
					#print("YES???")

					_new.add(str(key))
				else:
					#print("NOT???")
					_new.add("~" + str(key))

			#new = frozenset(_new)
			#print("Head Frozen: %s \n" % (_new))
			h_small_worlds.append(_new)

		for world in worlds:
			for small in h_small_worlds:
				#print("________small: %s world: %s" % (small, world.value))
				#if(small <= world.value):
				if(small.issubset(world.value) and world.name not in rule.setHeadExension):
					#print("Adding?")
					rule.setHeadExension.append(world.name)
					#print("Adding world %s to extension of %s" % (world.name, rule.name))
		

		b_small_worlds = []

		for item in rule.bodyExtension:
			_new = set()
			for key, value in item.items():
				#print("Is this working? \n")
				#print("Key: %s, Value %s" % (key, value))
				if(value == True):
					##print("YES???")
					_new.add(str(key))
				else:
					#print("NOT???")
					_new.add("~" + str(key))

			#new = frozenset(_new)
			#print("Body Frozen: %s \n" % (_new))
			b_small_worlds.append(_new)

		for world in worlds:
			for small in b_small_worlds:
				#print("________small: %s world: %s" % (small, world.value))
				if(small <= world.value and world.name not in rule.setBodyExension):
					#print("Adding?")
					rule.setBodyExension.append(world.name)
					#print("Adding world %s to extension of %s" % (world.name, rule.name))

			

			#rule.setBodyExension.add(new)
		

			
			'''for model in h_temp:
				for world in worlds:
					if model < world.state:
						rule.headExtension.append(world.state)'''


		'''for char in str(rule.head):
			if(char.isalpha()):
				add = Symbol(char)
				th1.add(add)
		th2 = propositions.difference(th1)

		item = ""
		for p in th2:
			item +=  "&" + "(" + str(p) + "|" +  "~" +  str(p) + ")"
		head_check = rule.head + item
		print("Head_check is: %s" % (head_check))
				
		h_temp = satisfiable(head_check, all_models = True)
		#for m in h_temp:
			#print("Here we go again: %s" % (m))
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
		tb2 = propositions.difference(tb1)
		item = ""
		for p in tb2:
			item +=  "&" + "(" +str(p) + "|" +  "~" +  str(p) + ")"
		body_check = rule.body + item
		print("Body check is: %s" % (body_check))
		b_temp = satisfiable(body_check, all_models = True)
		for model in b_temp:
			new = {}	
			for key in model:
				#print("Rule %s body issat by: %s: %s " % (rule.name, key, model[key]))
				new[key] = model[key]
			rule.bodyExtension.append(new)'''

def domination_relations(worlds, rules):
	for world in worlds:
		for k1, r1 in rules.items():
			for k2, r2 in rules.items():
				if(world.name not in r1.setBodyExension or world.name in r2.setBodyExension):
					if(world.name not in r1.setHeadExension or world.name not in r2.setHeadExension):
						if((world.name in r2.setBodyExension and world.name not in r1.setBodyExension) or \
						 (world.name in r1.setHeadExension or world.name in r2.setHeadExension)):
							new = (r1.name, r2.name)
							#print("add new dom")
							world.dom.add(new)


def assing_rule_violations(worlds, rules):
	for world in worlds:
		for k, rule in rules.items():
			if(world.name in rule.setBodyExension and world.name not in rule.setHeadExension):
				for d in world.dom:
					if(d[1] == rule.name):
						temp = rules[d[0]]
						if(world.state not in temp.bodyExtension):
							world.F.add(k)

def compareDict(a, b):
	Ka = set(a.keys())
	Kb = set(b.keys())
	Ba = set(a.values())
	Bb = set(b.values())
	V = (Ka == Kb) & (Ba == Bb)

def find_best_world():
	best_worlds = set()
	for w1 in worlds:
		check = True
		for w2 in worlds:
			if w1.F > w2.F:
				check = False
		if check == True:		
			#print("Check\n")
			best_worlds.add(w1.name)
	return best_worlds


print("__________________________________________________________________________\n")
print("Welcome to the Naive Preferences Solver\n")
print("___________________________________________________________________________\n")
file_name = input("Please input the name of a text-file containing a set of rules (include the 'txt' extension) \n")
print("Name of file: %s \n" % (file_name))

file = open(file_name, "r+")

#for line in file: 
#	print (line)

print("start")
#print(st)



propositions = obtain_atomic_formulas(file)
print("Propositions: %s \n" % (propositions))

file.seek(0)

rules = construct_rules_dict(file)

for k, v in rules.items():
	print(k, v.item)

worlds = construct_worlds(propositions)
for world in worlds:
	print("%s: %s \n" % (world.name, world.state))


'''for world in worlds:
	for v, k in world.state.items():
		print(v, k)'''

"""print("Worlds")
for world in worlds:
	print("%s: %s \n" % (world.name, world.state))"""


world_values(worlds)

for world in worlds:
	print(world.value)

assingn_rule_extensions(rules)

assign_sets_rules(rules)


#for k, rule in rules.items():
	#print("%s Body extension: %s\n" % (rule.name, rule.setBodyExension))
	#print("%s Head extension: %s\n" % (rule.name, rule.setHeadExension))

'''for v, rule in rules.items():
	#print(" %s is satisified by \n" % (rule.body))
	#print(len(rule.bodyExtension))
	#print(" %s is satisified by \n" % (rule.head))
	#print(len(rule.headExtension))
	for e in rule.setHeadExension:
		print("head %s true in  %s " % (rule.name, e))
		
	for e in rule.setBodyExension:
		print("body %s  true in %s " % (rule.name, e))'''

domination_relations(worlds, rules)

for world in worlds:
	for d in world.dom:
		#for p in d:
		print("%s in world %s \n" % (d, world.name))


assing_rule_violations(worlds, rules)
					
for world in worlds:
	for f in world.F:
		print("%s is violated in %s \n" % (f, world.name))


#Now we finally seek out the best worlds



best_worlds = find_best_world()


for w in best_worlds:
	print(w)






