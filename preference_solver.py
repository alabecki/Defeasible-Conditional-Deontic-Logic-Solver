#
#		Naive Preferences Solver_____________________________________________________________________________________________________________________________
#
#	The program reads txt files composed of rules in the following format:
#		(b, h), where a and b are formulas of propositional logic
#		b is the "body" of the rule, while h is the "head"
#		"&" is used for "and", "|" is used for "or", and "~" is used for negation
#		Example: ( (~P | (~Q | R)), (Q & P) )
#
#		The program makes use of the SAT solver included in sympy, which requires mpath
#		It also utilizes the Symbol object, with which formulas are encoded for the purpose of using the SAT solver
#
#
#		Import Libraries_____________________________________________________________________________________________________________________________________

from sympy import Symbol
from sympy.logic.inference import satisfiable
from mpmath import*
from itertools import product



commands = {
	"w": "Show the set of most perferable worlds",
	"c": "Compare two specific worlds",
	"d": "Debugging (or, more specific information)",
	"e": "I am done with this file"
}


debugging = {
	"1": "Show the world states at which a given rule is true",
	"2": "Show which rules are violated at a given world",
	"3": "Show which rules are false at a given world",
	"4": "Show which rules are varified at a given world",
	"5": "Show which rules are neutral relative to a given world",
	"6": "Show which domination relations obtain at a given world",
	"7": "Show the set of WORST worlds relative to the given rules"
}


#		Classes_______________________________________________________________________________________________________________________________________________
# One class is used to store attributes of rules and one class is used to sture attributes of worlds (states).

class Rule(object):
	def __init__(self, _name, _item, _body, _head):
		self.name = _name							# Name of rule for purpose of retrieval (r1, r2, ...)
		self.item = _item							# Item is the actual rule itself
		self.body = _body							# The body of the rule
		self.head = _head							# The head of the rule

		self.bodyExtension = []						# The partial worlds in which the head is verified (partial in that the worlds only include \
													# Propositions included in the rule
		self.headExtension = []						# Same as the bodyExtension, but applied to the head
		self.setHeadExension = []					# The set of worlds in which the head is true
		self.setBodyExension = []					# The set of worlds in which the body is true

class World(object):
	def __init__ (self, _name, _state):
		self.name = _name							# Name of the world (w1, w2, ...)
		self.state = _state							# The State of the world in the form of {A: True, B: False, .... }
		self.value = set()							# Precisely states which propositions are true/false in the world  {A, ~B, ...}
		self.F = set()								# The set of rules violated in the world
		self.dom = set()							# The set of domination relations between rules in the world



#		Functions_______________________________________________________________________________________________________________________________________________

# Scans the rule file for atomic formulas, this is needed to construct the worlds
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


# Parses each line of the rule file to create a a dictionary of rules, distinguishing the item, body and head. The key is the name of the rule
# while the value is the Rule object itself
def construct_rules_dict(file):
	lines = []
	for line in file:
		if line.startswith("("):
			#lines.append(line.rstrip("\n"))
			lines.append(line.strip())
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

# Uses the outout of obtain_atomic_formulas first create a table of boolean values corresponding to a world. It then constructs its "state" as a dictionary
# where the keys are propositions and the values are Booleans. The names and states are passed on as arguments to create a list of World objects.
def construct_worlds(propositions):
	num_worlds = list(range(2**len(propositions)))
	world_names = ["w" + str(i) for i in num_worlds]
	n = len(propositions)
	table = list(product([False, True], repeat=n))
	worlds = []
	count = 0
	for row in table:
		state = dict(zip(propositions, row))
		new = World(world_names[count], state)
		worlds.append(new)
		count +=1
	return worlds

# Since states are dictionaries, it is difficult to directly use them for determining when a formula is true in a given world, the states are
# used as a basis to produce the "value" of a world, which precisely a set of literals.
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


# The extension of the head/body of a rule is a set of states, where the states in question only include propositions contained in the actual formula
# These partial states are essentially of output of the SAT solver
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

# The extension obtained from assingn_rule_extensions() is used to assign each head/body of a rule a set of "small worlds" at which it is true
# (these are called "small_worlds" because they only contain propositions included in the head/body from which they are derived).
# Each member is like the "value" of a world in that it is a set of literals.
# We use these small_worlds to determine which rules are true in which worlds:
# When a small_word of a head/body is a subset of a world w, that the head/body is true in w (becaue it does not matter what assignments are
# given to the propositions not included in the small_worlds)
#
def assign_sets_rules(rules):
	for k, rule in rules.items():

		h_small_worlds = []
		for item in rule.headExtension:
			_new = set()
			for key, value in item.items():
				if(value == True):
					_new.add(str(key))
				else:
					_new.add("~" + str(key))
			h_small_worlds.append(_new)
		for world in worlds:
			for small in h_small_worlds:
				if(small.issubset(world.value) and world.name not in rule.setHeadExension):
					rule.setHeadExension.append(world.name)

		b_small_worlds = []
		for item in rule.bodyExtension:
			_new = set()
			for key, value in item.items():
				if(value == True):
					_new.add(str(key))
				else:
					_new.add("~" + str(key))
			b_small_worlds.append(_new)
		for world in worlds:
			for small in b_small_worlds:
				if(small <= world.value and world.name not in rule.setBodyExension):
					rule.setBodyExension.append(world.name)

# Now that that head/body of each rule is assigned a set of worlds, we can determine the domination relation in each world in a strightforward
# manner in terms of the definition of the relation
def domination_relations(worlds, rules):
	for world in worlds:
		for k1, r1 in rules.items():
			for k2, r2 in rules.items():
				if((world.name not in r1.setBodyExension or world.name in r2.setBodyExension) and \
					(world.name not in r1.setHeadExension or world.name not in r2.setHeadExension)):
						if((world.name in r2.setBodyExension and world.name not in r1.setBodyExension) or \
						(world.name in r1.setHeadExension or world.name in r2.setHeadExension)):
							new = (r1.name, r2.name)
							world.dom.add(new)


# We use the extensions assigned to rules and the domination relation to determine which rules are violated in each world
def assing_rule_violations(worlds, rules):
	for world in worlds:
		for k, rule in rules.items():
			if(world.name in rule.setBodyExension and world.name not in rule.setHeadExension):
				for d in world.dom:
					if(d[1] == rule.name):
						temp = rules[d[0]]
						if(world.state not in temp.bodyExtension):
							world.F.add(k)


def compare_worlds(u, v):
	a = int(u[1:])
	b = int(v[2:])
	print(a, b)
	if(worlds[a].F == worlds[b].F):
		print("%s and %s are equally preferable \n," % (worlds[a].name, worlds[b].name))
		return
	elif (worlds[a].F >= worlds[b].F):
		print("%s is preferable to %s \n" % (worlds[b].name, worlds[a].name))
		return
	elif worlds[b].F >= worlds[a].F:
		print("%s is preferable to %s \n" % (worlds[a].name, worlds[b].name))
		return
	else:
		print("%s and %s are not comparable in terms of preference \n" % (worlds[a].name, worlds[b].name))
		return


# We use the violation set see which worlds are best. Given the set of F (rule violations) for each world w, w1 is a "best" world if
# and only if there is no world w2 such that w1.F is a proper subset of w2.F (proper subset is used because we want to find those members
# that minimal accoring to the partial preorder defined in Definition 3.6)
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


def find_rule_extension(rule_name):
	result = dict()
	temp = rules[rule_name]
	for w in temp.setHeadExension:
		if w in temp.setBodyExension:
			temp2 = int(w[1:])
			result[worlds[temp2].name] = worlds[temp2].state
	return result

def print_violations(world_name):
	result = []
	temp = int(world_name[1:])
	for d in worlds[temp].F:
		result.append(d)
	return result

def print_false_rules_at_w(_world):
	result = []
	temp = int(_world[1:])
	for k, rule in rules.items():
		if(worlds[temp].name in rule.setBodyExension and worlds[temp].name not in rule.setHeadExension):
			result.append(rule.name)
	return result

def print_rules_true_at_w(_world):
	result = []
	temp = int(_world[1:])
	for k, rule in rules.items():
		if(worlds[temp].name in rule.setBodyExension and worlds[temp].name in rule.setHeadExension):
			result.append(rule.name)
	return result

def print_rules_neutral_at_w(_world):
	result = []
	temp = int(_world[1:])
	for k, rule in rules.items():
		if(worlds[temp].name not in rule.setBodyExension):
			result.append(rule.name)
	return result




#		Main____________________________________________________________________________________________________________________________________________________


print("__________________________________________________________________________\n")
print("Welcome to the Naive Preferences Solver\n")
print("___________________________________________________________________________\n")


while(True):
	print("What would you like to do? \n")
	do = input("(1) Open a file, (2), exit program\n")

	if(do == ("2")):
		break


	_file_name = input("Please input the name of a text-file containing a set of rules \n")

	file_name = _file_name + ".txt"

	print("Name of file: %s \n" % (file_name))

	file = open(file_name, "r+")

	print("Processing rules____________________________________________________________ \n")

	propositions = obtain_atomic_formulas(file)
	file.seek(0)

	rules = construct_rules_dict(file)

	for k, v in rules.items():
		print(k, v.item)

	worlds = construct_worlds(propositions)

	world_values(worlds)

	assingn_rule_extensions(rules)

	assign_sets_rules(rules)

	domination_relations(worlds, rules)

	assing_rule_violations(worlds, rules)

	_continue = True

	while(True):

		print("________________________________________________________________________________ \n")
		print(" What would you like to know? \n")

		for k, v in commands.items():
			print("%s: %s \n" % (k, v))
		com = input()
		if(com == "w"):
			best_worlds = find_best_world()
			print("\n")
			print(" The most preferred worlds are: %s \n" % (best_worlds))

		elif(com == "c"):
			print("Which two worlds would you like to compare? \n")
			for world in worlds:
				print("%s: %s \n" % (world.name, world.state))
			_pair = input("which two worlds would you like to compare? (write as: 'wi, wj', where i, j are integers) \n")
			pair = _pair.split(",")
			compare_worlds(pair[0], pair[1])
		elif(com == "d"):
			com1 = " "
			_choices = list(range(1, 7))
			choices = ''.join(str(e) for e in _choices)
			while (str(com1) not in choices):
				for k, v in debugging.items():
					print("%s: %s \n" % (k, v))
				com1 = input()
				if com1 == "1":
					print("For which rule would you like to make your query? (type in name) \n")
					for k, rule in rules.items():
						print("%s: %s \n" % (k, rule.item))
					_rule = input()
					result = find_rule_extension(_rule)
					print("%s is true in the following worlds:\n" % (_rules))
					for k, v in result.items():
						print(k, v)
				elif(com1 == "2"):
					print("For which world would you like to make your query? (type in name) \n")
					for world in worlds:
						print("%s: %s \n" % (world.name, world.state))
					print("For which world would you like to make your query? (type in name) \n")
					_world = input()
					result = print_violations(_world)
					print("World %s is violates the following rules:\n " % (_world))
					print(result)
				elif(com1 == "3"):
					print("For which world would you like to make your query?")
					for world in worlds:
						print("%s: %s \n" % (world.name, world.state))
					print("For which world would you like to make your query? (type in name) \n")
					_world = input()
					result = print_false_rules_at_w(_world)
					print("The following rules are false in " + _world)
					print(result)
				elif(com1 == "4"):
					print("For which world would you like to make your query?")
					for world in worlds:
						print("%s: %s \n" % (world.name, world.state))
					print("For which world would you like to make your query? (type in name) \n")
					_world = input()
					result = print_rules_true_at_w(_world)
					print("The following rules are true in " + _world)
					print(result)
				elif(com1 == "5"):
					print("For which world would you like to make your query?")
					for world in worlds:
						print("%s: %s \n" % (world.name, world.state))
					print("For which world would you like to make your query? (type in name) \n")
					_world = input()
					result = print_rules_neutral_at_w(_world)
					print("The following rules are neutral in " + _world)
					print(result)
				elif(com1 == "6"):
					print("For which world would you like to make your query?")
					for world in worlds:
						print("%s: %s \n" % (world.name, world.state))
					print("For which world would you like to make your query? (type in name) \n")
					_world = input()
					print("The following dominition relations between rules obtain in " + _world + " (where the left rule dominates the right): \n")
					temp = int(_world[1:])
					print(worlds[temp].dom)
				else:
					print("I'm sorry, you did not input a recognized command, please try again. \n")
		elif(com == "e"):
			break
		else:
			print("I'm sorry, you did not input a recognized command, please try again. \n")

		more = input("Would you like to make another query?  (y, n) \n")
		if(more == 'n'):
			break
