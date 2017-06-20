
from sympy import Symbol
from sympy.abc import*
from sympy.logic.boolalg import to_cnf
from sympy.logic.inference import satisfiable, valid
from sympy.logic.boolalg import Not, And, Or
from mpmath import*

from itertools import product
from preference_classes import Rule
from preference_classes import World
from preference_classes import Constraint
from preferences_query_functions import*
import os
import re
from copy import deepcopy

#		Functions_______________________________________________________________________________________________________________________________________________

#Prompts user to enter the name if a file, if the file does not exist, it reiterates.
def initiate(file):
	file.seek(0)
	propositions = obtain_atomic_formulas(file)
	#for p in propositions:					#fetches all atomic formulas found in a rule or constraint
		#print (p)
	file.seek(0)
	#rules = {}
	rules = construct_rules_dict(file)		# parses input text, make a Rule object for each rule, saves objects in dictionary
	file.seek(0)
	constraints = add_constraints(file)		#parses parces and saves contraints in a dictionary
	print("Rules: ")
	for k, v in rules.items():
		print(k, v.item)
	print("\n")
	print("Constraints: ")
	_worlds = construct_worlds(propositions)  #creates a dictionary of worlds
	for k, v in constraints.items():
		print(k, v.item)
	print("\n")
	worlds = reconstruct_worlds(propositions, constraints) #Next, exclude worlds that are prohibited by the constriants
	print("Worlds after constraints: \n")
	for w in worlds.values():
		print(w.state)
	for k, rule in rules.items():
		rule.bodyExtension = assign_extensions(rule.body, worlds, propositions)		#obtains extension of bodies of rules
		rule.headExtension = assign_extensions(rule.head, worlds, propositions)		#obtains extensions of heads of rules
	domination_relations(rules)									#assigns each rule the set of rules that dominate it
	assign_rule_violations(worlds, rules)						#Assigns a set of rule violations to each world
	#assign_rule_violations_recursive(worlds, rules)
	#assign_dependencies(worlds)									#(Not currently used - might use later for printing partial ordering)
	data = [propositions, rules, constraints, worlds]
	return data


def get_file():
	while True:
		file_name = input("Please input the name of a text-file containing a set of rules \n")
		file_name = file_name + ".txt"
		if(os.path.exists(file_name)):
			_file = open(file_name, "r+")
			print("Name of file: %s \n" % (file_name))
			res = [_file, file_name]
			return res
		else:
			print("The file you selected does not exist, please try again\n")
            #filename = input("Select the first/second/third file:")

# Scans the rule file for atomic formulas (letters). This is needed to construct the worlds
def obtain_atomic_formulas(file):
	propositions = set()
	for line in file:
		if line.startswith("(") or line.startswith("!"):
			prop_char = set()
			for char in line:
				#print(str(char))
				if(str(char).isalpha()) and str(char) not in ["N", "o", "t"]:
					prop_char.add(str(char))
			for item in prop_char:
				new = Symbol(item)
				propositions.add(new)
	return propositions						#returns the set of propositions involved in the set of rules


def delete_file_content(pfile):
    pfile.seek(0)
    pfile.truncate()

# Parses each line of the rule file to create a dictionary of rules, distinguishing the item, body and head. The key is the name of the rule
# while the value is the Rule object itself
def construct_rules_dict(file):
	lines = []
	for line in file:
		line = line.strip()
		if line.startswith("("):
			line = re.sub(r'\s+', '', line)
			lines.append(line.strip())
	steps = []
	for line in lines:
		steps.append(re.split("->|\$", line))
	for step in steps:
		step[0] = step[0][1:]

		step[1] = step[1][:-1]
	rules = {}
	count = 0
	for line in steps:
		name = "r" + str(count)
		if len(line) == 2:
			item = line[0] + " -> " + line[1]
			new = Rule(name, item, line[0], line[1])
		if len(line) == 3:
			item = line[0] + " -> " + line[1] +  " $ " + line[2]
			new = Rule(name, item, line[0], line[1], float(line[2]))
		rules.update({name: new})
		count += 1
	return rules


def add_rule(rule, rules):
	rule = rule.strip()
	rule = re.sub(r'\s+', '', rule)
	step = (re.split("->|\$", rule))
	#print("Step 0 %s " % (step[0]))
	#print("Step 1 %s " % (step[1]))
	step[0] = step[0][1:]
	step[1] = step[1][:-1]
	count = len(rules)
	name = "r" + str(count)
	if len(step) == 1:
		item = " " + " -> " + step[0]
		new = Rule(name, item, " " , step[0])
	if len(step) == 2:
		item = step[0] + " -> " + step[1]
		new = Rule(name, item, step[0], step[1])
	if len(step) == 3:
		item = step[0] + " -> " + step[1] +  " $ " + step[2]
		new = Rule(name, item, step[0], step[1], float(step[2]))
	rules.update({name: new})

def add_constraints(file):
	lines = []
	for line in file:
		line.strip()
		line = re.sub(r'\s+', '', line)
		if line.startswith("!"):
			lines.append(line.strip())
		#for line in lines:
	temp1 = [line[1:] for line in lines]		#remove "!(" at the beginning of the rule
	#temp2 = [line[:-1] for line in temp1]		#remove the ")" at the end of the rule
	constraints = {}
	count = 0
	for line in temp1:
		name = "c" + str(count)
		new = Constraint(name, line)
		constraints.update({name: new})
		count += 1
	return constraints

# Uses the output of obtain_atomic_formulas first create a table of Boolean values corresponding to a world. It then constructs its "state" as a dictionary
# where the keys are propositions and the values are Booleans. The names and states are passed on as arguments to create a list of World objects.
def construct_worlds(propositions):
	_op = []
	for p in propositions:
		_op.append(str(p))
	_op.sort()
	op = []
	for o in _op:
		new = Symbol(o)
		op.append(new)
	num_worlds = list(range(2**len(propositions)))	#calculates number of rows in the table from which the worlds will be obtained
	world_names = ["w" + str(i) for i in num_worlds]	#creates a unique name for each world: "w" plus an integer
	n = len(propositions)								#number of propositions for table creation
	table = list(product([False, True], repeat=n))		#creation of a truth table
	worlds = {}											#initiates an empty list of worlds
	count = 0
	for row in table:
		state = dict(zip(op, row))
		name = world_names[count]			#each state is a dictionary associating a truth value with each propositional
		new = World(name, state)			#new world object is created with the name and state as attributes
		worlds[name] = new								#the new world is added to the list of worlds
		count +=1
	return worlds


# Assigns each rule head and rule body a set of possible worlds, namely those in which it is true
#Since a given rule body/head will typically not include all atomic propositions found within the rule-set, directly applying  #a SAT solver on this formula will not give us the worlds we are looking for, since each world should assign truth values to  #all propositions found in the rule-set. So given a body/head x, if P is a proposition found in the set of rules but not in x, #then x will be augmented with &(P | ~P).
def assign_extensions(formula, worlds, propositions):
	extension = []
	if str(formula).isspace() or len(formula) == 0:			#if the formula is empty it will be treated as a toutology
		#print("Check Empty\n")
		for w in worlds.values():
			extension.append(w.state)
		return extension
	else:
		props_in_formula = set()		#store propositions found in the formula
		for char in str(formula):
			add = Symbol(char)
			props_in_formula.add(add)
		props_not_in_form = propositions.difference(props_in_formula)	#Determine which propositions are missing from the rule's body
		supplement = Symbol('')
		form_cnf = to_cnf(formula)
		for p in props_not_in_form:
			supplement = Or(p, Not(p))							#Loop aguments (P | ~P) for each P not found in body
			form_cnf = And(form_cnf, supplement)
		#print("__form_cnf: %s \n" % (form_cnf))
		form_SAT = satisfiable(form_cnf, all_models = True)  #The sympy SAT solver is applied to the augmented formula
		form_SAT_list = list(form_SAT)				       #the ouput of satisfiable() is an itterator object so we turn it into a list
		if(len(form_SAT_list) == 1 and form_SAT_list[0] == False):		#check to handle inconsistencies
			extension = []
			return extension
		else:
			for state in form_SAT_list:		#We now turn each state in which the body is true into a dictionary so that
				new = {}						#they may be directly compared with each world state
				#if get_world_from_state(state, worlds) == None:
					#continue
				#else:
				for key, value in state.items():
					new[key] = value
					extension.append(new)
	return extension


# Now that that head/body of each rule is assigned a set of world states, we can determine the domination relation
#in each world in a straightforward manner in terms of the definition of the relation
def domination_relations(rules):
	#print("Calculating Domination Relations______________________________________________________________________________\n")
	dominations = set()
	for k1, r1 in rules.items():	#and compare each rule with each of the others
		for k2, r2 in rules.items():
				#The following simply applies the definition of rule domination to the extensions of the rules in each world
				#First check for "improper" domination
			if not r1.body and not r2.body:
				#(str(r1.body).isspace() or str(r2.body).isspace() ):
				continue
			#if str(r1.body).isspace():
			if not r1.body: #To process rules without conditions
				continue
			elif not r2.body:  # If r2 does not have a body will generally be dominated by r1 when the two heads collide
			#str(r2.body).isspace():
				r1h_cnf = to_cnf(r1.head)
				r2h_cnf = to_cnf(r2.head)
				temp3 = And(r1h_cnf, r2h_cnf )
				notbothheads = Not(temp3)
				if valid(notbothheads) == True:
					r2.dominatedBy.add(r1)
			else:
				r1b_cnf = to_cnf(r1.body)  #convert formulats to CNF for SAT solving
			#	print(r2.body)
				r2b_cnf = to_cnf(r2.body)
				r1h_cnf = to_cnf(r1.head)
				r2h_cnf = to_cnf(r2.head)
				temp1 = Not(r1.body)		#putting together formulas for testing the domination condition
				temp2 = Not(r2.body)
				r1b_r2b = Or(temp1, r2b_cnf)
				r2b_r1b = Or(temp2, r1b_cnf)
				temp3 = And(r1h_cnf, r2h_cnf )
				notbothheads = Not(temp3)
				#print("First: %s, %s \n" % (r1b_r2b, notbothheads) )
				if((valid(r1b_r2b) == True) and valid(notbothheads) == True):
					if(valid(r2b_r1b) == False or valid(notbothheads) == False):
						new = (r1.name, r2.name)
						dominations.add(new)
						if (r2.item != r1.item):
							r2.dominatedBy.add(r1)

# We use the extensions assigned to rules and the domination relations to determine which rules are violated in each world
def dom_dom_check(world, rule, flag):
	for dom in rule.dominatedBy:
		#print("Dominated by %s\n" % (dom.name
		if(world.state not in dom.bodyExtension):
			#print("In recursion: this dom %s is neutral \n" % (dom.name))
			continue
		else:
			#print("This dom %s is not neutral \n" % (dom.name))
			flag = flag + 1
			#print("%s overides.... \n" % (dom.name))
			#print("Flag in rec: %s \b" % (flag))
			dom_dom_check(world, dom, flag)
	#print("About to return from recursion")
	return flag


def assign_rule_violations(worlds, rules):
#	print("Assigning rule violations __________________________________________________________________________________")
	for world in worlds.values():
		for k, rule in rules.items():
			#First check if the rule is False in the world under consideration
			if(world.state in rule.bodyExtension and world.state not in rule.headExtension):
			#Now make sure that, if the rule is dominated by any other rules in this world, then that other rule
			#is Neutral in this world.
				if len(rule.dominatedBy) == 0:
					world.F.add(k)
					world.weightedF += rule.weight
				else:
					flag = False
					for dom in rule.dominatedBy:
						if (world.state in dom.bodyExtension):
							flag = True
					if flag == False:
						world.F.add(k)
						world.weightedF += rule.weight


def assign_rule_violations_recursive(worlds, rules):
#print("Assigning rule violations ________________________________________________________________________________")
	for world in worlds.values():
		for k, rule in rules.items():
			#First check if the rule is False in the world under consideration
			if(world.state in rule.bodyExtension and world.state not in rule.headExtension):
			#Now make sure that, if the rule is dominated by any other rules in this world, then that other rule
			#is Neutral in this world.
				flag = 0
				for dom in rule.dominatedBy:
					if (world.state not in dom.bodyExtension):
						continue
					flag += 1
					#print("Flag before recusion %s \n" % (flag))
					flag = dom_dom_check(world, dom, flag)
					#print("Just got back from recusion and flag is %s \n" % (flag))
				if flag % 2 == 0:
					world.F.add(k)
					world.weightedF += rule.weight
				else:
					continue

# We use the violation set F to see which worlds are best. Given the set of F (rule violations) for each world w, w1 is a #"best" world if and only if there is no world w2 such that w1.F is a proper subset of w2.F.
def best_worlds_by_subset(worlds):
	best_worlds = {}
	for w1 in worlds.values():
		check = True
		for w2 in worlds.values():
			if w1.F > w2.F:
				check = False
		if check == True:
			best_worlds[w1.name] = w1
			#best_worlds.add(w1.name)
	return best_worlds


# Assigns to each world those worlds which would be its children if a tree were to be constucted to show the
# partial order of worlds relative to sets of rule violations
def assign_dependencies(worlds):
	for w1, world1 in worlds.items():
		for w2, world2 in worlds.items():
			if world1.F.issubset(world2.F) and (len(world2.F) - len(world1.F)) == 1:
				world1.dependency.add(world2)

#Presents the best worlds in terms of the cardinality of rule violations
def best_worlds_by_cardinality(worlds):
	best_worlds = {}
	sorted_worlds = sorted(worlds.values(), key =lambda x: len(x.F))
	best = len(sorted_worlds[0].F)
	for i in sorted_worlds:
		if(len(i.F) > best):
			return best_worlds
		else:
			best_worlds[i.name] = i

# Orders the worlds by summing the weights of the rules violated in each
def best_worlds_by_weighted_cardinality(worlds):
	best_worlds = {}
	sorted_worlds = sorted(worlds.values(), key =lambda x: x.weightedF)
	best = sorted_worlds[0].weightedF
	for w in sorted_worlds:
		if w.weightedF > best:
			return best_worlds
		else:
			best_worlds[w.name] = w


def add_proposition(propositions, p):
	for char in p:
		if (str(char).isalpha()):
			propositions.add(Symbol(char))

#Used to reconstruct worlds in light of any constraints that might be included in the file
def reconstruct_worlds(propositions, constraints):
	_worlds2 = construct_worlds(propositions)
	for k, constraint in constraints.items():
		constraint.extension = assign_extensions(constraint.item, _worlds2, propositions)
	worlds2 = {}
	flag = True
	for w, world in _worlds2.items():
		flag = True
		for constraint in constraints.values():
		#	print("World: %s, constraint %s \n" % (world.state, constraint.item))
			if world.state not in constraint.extension:
				flag = False
		if flag == True:
			worlds2[w] = world
	return worlds2

# Used to find the best f-worlds when evaluated in terms of w.F subsets
def get_min_F_subset(f_ext, worlds):
	f_min = set()
	for e1 in f_ext:
		w1 = get_world_from_state(e1, worlds)
		if w1 != None:
			f_min.add(worlds[w1])
			for e2 in f_ext:
				w2 = get_world_from_state(e2, worlds)
				if w2 != None:
					if worlds[w2].F < worlds[w1].F:
						f_min.remove(worlds[w1])
						break
	return f_min

# Used to find the best f-worlds when evaluated in terms of the weighted cardinality of rule violations
def get_min_F_weight(f_ext, worlds):
	f_min = set()
	best = 99999999
	for w in f_ext:
		world = get_world_from_state(w, worlds)
		if world != None:
			if worlds[world].weightedF < best:
				best = worlds[world].weightedF
	for w in f_ext:
		world = get_world_from_state(w, worlds)
		if world != None:
			if worlds[world].weightedF == best:
				f_min.add(worlds[world])
	return f_min

# Used to find the best f-worlds when evaulated in terms of the cardinality of rule violations
def get_min_F_card(f_ext, worlds):
	f_min = set()
	best = 99999999
	for w in f_ext:
		world = get_world_from_state(w, worlds)
		if world != None:
			if len(worlds[world].F) < best:
				best = len(worlds[world].F)
	for w in f_ext:
		world = get_world_from_state(w, worlds)
		if world != None:
			if len(worlds[world].F) == best:
				f_min.add(worlds[world])
	return f_min


# Used to determine whether, given R, if  O(a |- b)
def obligation_implication(f1_min, f2ext, worlds):
	Flag = True
	for w in f1_min:
		if w.state not in f2ext:
			Flag = False
			return False
	if Flag == True:
		return True
	else:
		return False

# Used to determine whether, given R, if  P(a |- b)
def permissable_implication(f1_min, f2ext, worlds):
	Flag = False
	for w in f1_min:
		if w.state in f2ext:
			Flag = True
			return True
	if Flag == True:
		return True
	else:
		return False

# Used to determine whether a rule, provided by user input, is implied by those already given
def implicit_rule(r, worlds, worlds2, propositions2, rules2):
	add_rule(r, rules2)
	for k, rule in rules2.items():
		rule.bodyExtension = assign_extensions(rule.body, worlds2, propositions2)
		rule.headExtension = assign_extensions(rule.head, worlds2, propositions2)
	domination_relations(rules2)
	assign_rule_violations(worlds2, rules2)
	flag = True
	for w2i, world2i in worlds2.items():
		for w2j, world2j in worlds2.items():
			if w2i == w2j:
				continue
			if world2i.F.issubset(world2j.F):
				print("new- sub")
				print(w2i, world2i.F, w2j, world2j.F)
				print("old")
				print(worlds[w2i].F, worlds[w2j].F)
				if worlds[w2j].F.issubset(worlds[w2i].F) and worlds[w2j].F != worlds[w2i].F:
					return False

			if world2j.F.issubset(world2i.F) and world2i.F != world2j.F:
				print("new- sub")
				print(w2i, world2i.F, w2j, world2j.F)
				print("old")
				print(worlds[w2i].F, worlds[w2j].F)
				if worlds[w2i].F.issubset(worlds[w2j].F) and worlds[w2j].F != worlds[w2i].F:
					return False

			if worlds[w2i].F.issubset(worlds[w2j].F) and w2i != w2j:
				print("new- sub")
				print(w2i, world2i.F, w2j, world2j.F)
				print("old")
				print(worlds[w2i].F, worlds[w2j].F)
				if world2j.F.issubset(world2i.F) and world2j.F != world2i.F:
					return False

			if worlds[w2j].F.issubset(worlds[w2i].F):
				print("new- sub")
				print(w2i, world2i.F, w2j, world2j.F)
				print("old")
				print(worlds[w2i].F, worlds[w2j].F)
				if world2i.F.issubset(world2j.F)  and world2j.F != world2i.F:
					return False

			if world2i.F.issubset(world2j.F) == False:
				print("new- sub")
				print(w2i, world2i.F, w2j, world2j.F)
				print("old")
				print(worlds[w2i].F, worlds[w2j].F)
				if worlds[w2i].F.issubset(worlds[w2j].F):
					flag = False
					return flag
			if world2j.F.issubset(world2i.F) == False:
				print("new- sub")
				print(w2i, world2i.F, w2j, world2j.F)
				print("old")
				print(worlds[w2i].F, worlds[w2j].F)
				if worlds[w2j].F.issubset(worlds[w2i].F):
					flag = False
					return flag

			if worlds[w2j].F.issubset(worlds[w2i].F) == False:
				print("new- sub")
				print(w2i, world2i.F, w2j, world2j.F)
				print("old")
				print(worlds[w2i].F, worlds[w2j].F)
				if world2j.F.issubset(world2i.F):
					flag = False
					return flag

			if worlds[w2i].F.issubset(worlds[w2j].F) == False:
				print("new- sub")
				print(w2i, world2i.F, w2j, world2j.F)
				print("old")
				print(worlds[w2i].F, worlds[w2j].F)
				if world2i.F.issubset(world2j.F):
					flag = False
					return flag
	return True
