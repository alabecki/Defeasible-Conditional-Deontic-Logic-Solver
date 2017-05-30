
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
import os
import re
from copy import deepcopy

#		Functions_______________________________________________________________________________________________________________________________________________

#Prompts user to enter the name if a file, if the file does not exist, it reiterates.

def get_file():
	while True:
		file_name = input("Please input the name of a text-file containing a set of rules \n")
		file_name = file_name + ".txt"
		if(os.path.exists(file_name)):
			_file = open(file_name, "r+")
			print("Name of file: %s \n" % (file_name))
			return _file
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
				if(str(char).isalpha()):
					prop_char.add(str(char))
			for item in prop_char:
				new = Symbol(item)
				propositions.add(new)
	return propositions						#returns the set of propositions involved in the set of rules


# Parses each line of the rule file to create a a dictionary of rules, distinguishing the item, body and head. The key is the name of the rule
# while the value is the Rule object itself
def construct_rules_dict(file):
	lines = []
	for line in file:
		if line.startswith("("):				#any line starting with a "(" is interpreted as a rule
			lines.append(line.strip())
	temp1 = [line[1:] for line in lines]		#remove "(" at the beginning of the rule
	temp2 = [line[:-1] for line in temp1]		#remove the ")" at the end of the rule
	temp3 = [line.split(",") for line in temp2]		#split into body and head
	rules = {}										#rules will be kept in a dictionary for easy look-up
	count = 0										#used to assign each rule with a unique name
	for line in temp3:
		item = line[0] + "," + line[1]				#stores the original rule
		name = "r" + str(count)						#gives each rule a unique name "r" plus an integer
		new = Rule(name, item, line[0], line[1])	#creates a new Rule object there line[0] and line[1] are the body and head
		rules.update({name: new})					#adds the new rule to the dictionary of rules
		count += 1
	return rules

def add_rule(rule, rules):
	count = len(rules) + 1
	temp1 = rule[1:]
	temp2 = temp1[:-1]
	temp3 = temp2.split(",")
	print("New body: %s, new head: %s \n" % (temp3[0], temp3[1]))
	item = temp3[0] + "," + temp3[1]
	name = "r" + str(count)
	new = Rule(name, item, temp3[0], temp3[1])
	rules.update({name: new})


def add_constraints(file):
	lines = []
	for line in file:
		if line.startswith("!"):
			lines.append(line.strip())
		for line in lines:
			print("WTF?")
			print(line)
	temp1 = [line[1:] for line in lines]		#remove "!(" at the beginning of the rule
	#temp2 = [line[:-1] for line in temp1]		#remove the ")" at the end of the rule
	constraints = {}
	count = 0
	for line in temp1:
		print(temp1)
		name = "c" + str(count)
		new = Constraint(name, line)
		constraints.update({name: new})
		count += 1
	return constraints


# Uses the output of obtain_atomic_formulas first create a table of Boolean values corresponding to a world. It then constructs its "state" as a dictionary
# where the keys are propositions and the values are Booleans. The names and states are passed on as arguments to create a list of World objects.
def construct_worlds(propositions):
	num_worlds = list(range(2**len(propositions)))	#calculates number of rows in the table from which the worlds will be obtained
	world_names = ["w" + str(i) for i in num_worlds]	#creates a unique name for each world: "w" plus an integer
	n = len(propositions)								#number of propositions for table creation
	table = list(product([False, True], repeat=n))		#creation of a truth table
	worlds = {}											#initiates an empty list of worlds
	count = 0
	for row in table:
		state = dict(zip(propositions, row))
		name = world_names[count]			#each state is a dictionary associating a truth value with each propositional
		new = World(name, state)			#new world object is created with the name and state as attributes
		worlds[name] = new								#the new world is added to the list of worlds
		count +=1
	return worlds

# Assigns each rule head and rule body a set of possible worlds, namely those in which it is true
#Since a given rule body/head will typically not include all atomic propositions found within the rule-set, directly applying  a
# SAT solver on this formulas will not give us the worlds we are looking for, since each world should assign truth values to all
# propositions found in the rule-set. So given a body/head x, if P is a proposition found in the set of rules but not in x, then x will be
#augmented with &(P | ~P).

def assign_extensions(formula, worlds, propositions):
	extension = []
	if str(formula).isspace():			#if the formula is empty it will be treated as a toutology
		print("Check Empty\n")
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
		#print("Formula: %s " % (formula))
		print("Formula: %s \n " % (formula))
		print("Prop not in form: %s \n " % (props_not_in_form))
		form_cnf = to_cnf(formula)
		#print("cnf: %s \n " % (form_cnf))
		print(form_cnf)
		for p in props_not_in_form:
			supplement = Or(p, Not(p))
			#print("form_cnf: %s, supplement: %s \n" % (form_cnf, supplement) )							#Loop aguments (P | ~P) for each P not found in body
			form_cnf = And(form_cnf, supplement)
		#print("__form_cnf: %s \n" % (form_cnf))
		print(form_cnf)
		form_SAT = satisfiable(form_cnf, all_models = True)  #The sympy SAT solver is applied to the augmented formula
		form_SAT_list = list(form_SAT)				       #the ouput of satisfiable() is an itterator object so we turn it into a list
		if(len(form_SAT_list) == 1 and form_SAT_list[0] == False):		#check to handle inconsistencies
			extension = []
			return extension
		else:
			for state in form_SAT_list:			#We now turn each state in which the body is true into a dictionary so that
				new = {}						#they may be directly compared with each world state
				for key, value in state.items():
					new[key] = value
				extension.append(new)
	return extension


# Now that that head/body of each rule is assigned a set of world states, we can determine the domination relation
#in each world in a straightforward manner in terms of the definition of the relation
def domination_relations(rules, dominations):
	print("Calculating Domination Relations___________________________________________________________________________________\n")
	for k1, r1 in rules.items():	#and compare each rule with each of the others
		for k2, r2 in rules.items():
				#The following simply applies the definition of rule domination to the extensions of the rules in each world
				#First check for "improper" domination
				#r1b = set(r1.bodyExtension)
				#r2b = set(r2.bodyExtension)
			print(r1.body, r2.body)
			if (str(r1.body).isspace() or str(r2.body).isspace() ):
			#	print("Check if either one has empty body")
				continue
			else:
				r1b_cnf = to_cnf(r1.body)
				r2b_cnf = to_cnf(r2.body)
				r1h_cnf = to_cnf(r1.head)
				r2h_cnf = to_cnf(r2.head)
				temp1 = Not(r1.body)
				temp2 = Not(r2.body)
				r1b_r2b = Or(temp1, r2b_cnf)
				r2b_r1b = Or(temp2, r1b_cnf)
				temp3 = And(r1h_cnf, r2h_cnf )
				notbothheads = Not(temp3)
				#print("First: %s, %s \n" % (r1b_r2b, notbothheads) )
				if((valid(r1b_r2b) == True) and valid(notbothheads) == True):
					#print("D Check 2\n")
					#print("Second: %s, %s \n" % (r2b_r1b, notbothheads))
					if(valid(r2b_r1b) == False or valid(notbothheads) == False):
						#print("D Check 3\n")
						new = (r1.name, r2.name)

						dominations.add(new)
						if (r2.item != r1.item):
							r2.dominatedBy.add(r1)


# We use the extensions assigned to rules and the domination relations to determine which rules are violated in each world
def dom_dom_check(world, rule, flag):
	for dom in rule.dominatedBy:
		#print("Dominated by %s\n" % (dom.name))
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


def assign_rule_violations(worlds, rules, dominations):
	print("Assigning rule violations ________________________________________________________________________________")
	for world in worlds.values():
		print(world.state)
		for k, rule in rules.items():
			print(k)
			#First check if the rule is False in the world under consideration
			if(world.state in rule.bodyExtension and world.state not in rule.headExtension):
			#	print("%s is false in %s \n" % (rule.name, world.state ))
			#Now make sure that, if the rule is dominated by any other rules in this world, then that other rule
			#is Neutral in this world.
				flag = 0
				for dom in rule.dominatedBy:
					#print("Next dom: %s \n " % (dom.name))
					if (world.state not in dom.bodyExtension):
					#	print("This dom %s neutral \n" % (dom.name))
						continue
				#	print("About to send %s into recursion \n" % (dom.name))
					flag += 1
					#print("Flag before recusion %s \n" % (flag))
					flag = dom_dom_check(world, dom, flag)
				#	print("Just got back from recusion and flag is %s \n" % (flag))
				if flag % 2 == 0:
					#print("Final Flag: %s \b" % (flag))
					#print("%s violates %s \n" % (world.state, k))
					world.F.add(k)
				else:
					continue

# We use the violation set F to see which worlds are best. Given the set of F (rule violations) for each world w, w1 is a "best" world if
# and only if there is no world w2 such that w1.F is a proper subset of w2.F (proper subset is used because we want to # find those members that minimal according to the partial preorder defined in Definition 3.6)
def find_best_world(worlds):
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


def add_proposition(propositions, p):
	for char in p:
		if (str(char).isalpha()):
			propositions.add(Symbol(char))


def check_inference(f1ext, f2ext, best_worlds, worlds):
	Flag = True
	for k, w in best_worlds.items():
		if w.state in f1ext and not w.state in f2ext:
			Flag = False
	if Flag == True:
		return True
	else:
		return False


def implicit_rule(r, best_worlds, rules2, worlds2, propositions2):
	#first add r as a new rule
	add_rule(r, rules2)
	for k, rule in rules2.items():
		rule.bodyExtension = assign_extensions(rule.body, worlds2, propositions2)
		rule.headExtension = assign_extensions(rule.head, worlds2, propositions2)
	dominations2 = set()
	domination_relations(rules2, dominations2)
	assign_rule_violations(worlds2, rules2, dominations2)
	new_best_worlds = find_best_world(worlds2)
	print("New best worlds: \n")
	for k, v in new_best_worlds.items():
		print("%s: %s \n" % (k, v.state))
	print("Old best  worlds: \n")
	for k, v in best_worlds.items():
		print("%s: %s \n" % (k, v.state))
	old = set(best_worlds.keys())
	new = set(new_best_worlds.keys())


	if old == new:
		return True
	else:
		return False
