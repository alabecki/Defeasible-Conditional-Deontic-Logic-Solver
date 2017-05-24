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
from sympy.abc import*
from sympy.logic.boolalg import to_cnf
from sympy.logic.boolalg import Not, And, Or
from sympy.logic.inference import satisfiable
from mpmath import*
from itertools import product
import sys
from copy import deepcopy

import re
from preference_functions import*
from preference_classes import Rule
from preference_classes import World
from preference_classes import Constraint


commands = {
	"w": "Show the set of most preferable  worlds",
	"c": "Compare two specific worlds with resepect to preference",
	"d": "Additional Queries",
	"e": "I am done with this file"
}

debugging = {
	"1": "Show the world states at which a given rule is true",
	"2": "Show the world states at which a given rule is violated",
	"3": "Show which rules are violated at a given world",
	"4": "Show which rules are false at a given world",
	"5": "Show which rules are verified  at a given world",
	"6": "Show which rules are neutral relative to a given world",
	"7": "Show which domination relations obtain at a given world",
	"8": "Show the worlds that violate the most rules",
	"9": "Show the body extension of a rule",
	"10": "Show the head extension of a rule",
	"11": "For a given r/w pair, show which rules dominate r in w",
	"12": "Check if world w is in body extension of a rule r",
	"13": "Check if world w is in head extension of a rule r",
	"14": "Print body of a rule",
	"15": "Prind head of a rule"
}

#		Main____________________________________________________________________________________________________________________________________________________


print("__________________________________________________________________________\n")
print("Welcome to the Naive Preferences Solver\n")
print("___________________________________________________________________________\n")


while(True):
	do = ""
	print("What would you like to do? \n")
	while(do != "1" and do !="2"):
		do = input("(1) Open a file, (2), exit program\n")
		if(do == "2"):
			sys.exit()
		if(do == "1"):
			file = get_file()
			#file_name = _file_name + ".txt"
		else:
			print("I'm sorry, could you repeat your command? \n")


	print("Processing rules____________________________________________________________ \n")


	propositions = obtain_atomic_formulas(file)

	file.seek(0)

	rules = construct_rules_dict(file)		#parces input text, make a Rule object for each rule, saves objects in dictionary

	file.seek(0)

	constraints = add_constraints(file)		#parces and saves contraints in a dictionary

	for k, v in rules.items():
		print(k, v.item)

	_worlds = construct_worlds(propositions)


	for k, constraint in constraints.items():
		constraint.extension = assign_extensions(constraint.item, _worlds, propositions)
		for ext in constraint.extension:
			print(" %s : %s \n" % (k, ext))

	worlds = {}

	flag = True
	for w, world in _worlds.items():
		flag = True
		for constraint in constraints.values():
			for ext in constraint.extension:
				if world.state == ext:
					print("Check if equal \n")
					flag = False
		if flag == True:
				worlds[w] = world


	for w in worlds.values():
		print(w.state)



	for k, rule in rules.items():
		rule.bodyExtension = assign_extensions(rule.body, worlds, propositions)
		rule.headExtension = assign_extensions(rule.head, worlds, propositions)


	domination_relations(worlds, rules)

	assign_rule_violations(worlds, rules)

	_continue = True

	while(True):

		print("________________________________________________________________________________ \n")
		print(" What would you like to know? \n")

		for k, v in commands.items():
			print("%s: %s \n" % (k, v))
		com = input()
		if(com == "w"):
			best_worlds = find_best_world(worlds)
			print("\n")
			print(" The most preferred worlds are: \n")
			for k, v in best_worlds.items():
				print("%s: %s \n" % (k, v))

		elif(com == "c"):
			print("Which two worlds would you like to compare? \n")
			for world in worlds.values():
				print("%s: %s \n" % (world.name, world.state))
			_pair = input("which two worlds would you like to compare? (write as: 'wi, wj', where i, j are integers) \n")
			pair = _pair.split(",")
			compare_worlds(pair[0], pair[1], worlds)
		elif(com == "d"):
			com1 = " "
			_choices = list(range(1, 16))
			choices = ''.join(str(e) for e in _choices)
			while (str(com1) not in choices):
				for k, v in debugging.items():
					print("%s: %s \n" % (k, v))
				com1 = input()
				if com1 == "1":
					print("For which rule would you like to make your query? (type in name) \n")
					for k, rule in rules.items():
						print("%s: %s \n" % (k, rule.item))
					_rule =  check_rule_input(rules)
					result = find_rule_extension(_rule, rules, worlds)
					print("%s is true in the following worlds:\n" % (_rule))
					for w in result:
						print(w)
				elif(com1 == "2"):
					print("For which rule would you like to make your query? (type in name) \n")
					for k, rule in rules.items():
						print("%s: %s \n" % (k, rule.item))
					_rule =  check_rule_input(rules)
					result = find_rule_violations(_rule, rules, worlds)
					if (result) == {}:
						print("%s is not violated in any world" % (_rule))
					else:
						print("%s is violated in the following worlds:\n" % (_rule))
						for w in result:
							print("%s : %s \n" % (w.name, w.state))

				elif(com1 == "3"):
					print("For which world would you like to make your query? (type in name) \n")
					for world in worlds.values():
						print("%s: %s \n" % (world.name, world.state))
					print("For which world would you like to make your query? (type in name) \n")
					_world =check_world_input(worlds)
					result = print_violations(_world, worlds)
					print("World %s violates the following rules:\n " % (_world))
					print(result)
				elif(com1 == "4"):
					print("For which world would you like to make your query?")
					for world in worlds.values():
						print("%s: %s \n" % (world.name, world.state))
					print("For which world would you like to make your query? (type in name) \n")
					_world =check_world_input(worlds)
					result = print_false_rules_at_w(_world, rules, worlds)
					print("The following rules are false in " + _world)
					print(result)
				elif(com1 == "5"):
					print("For which world would you like to make your query?")
					for world in worlds.values():
						print("%s: %s \n" % (world.name, world.state))
					print("For which world would you like to make your query? (type in name) \n")
					_world =check_world_input(worlds)
					result = print_rules_true_at_w(_world, rules, worlds)
					print("The following rules are true in " + _world)
					print(result)
				elif(com1 == "6"):
					print("For which world would you like to make your query?")
					for world in worlds.values():
						print("%s: %s \n" % (world.name, world.state))
					print("For which world would you like to make your query? (type in name) \n")
					_world =check_world_input(worlds)
					result = print_rules_neutral_at_w(_world, rules, worlds)
					print("The following rules are neutral in " + _world)
					print(result)
				elif(com1 == "7"):
					print("For which world would you like to make your query?")
					for world in worlds.values():
						print("%s: %s \n" % (world.name, world.state))
					print("For which world would you like to make your query? (type in name) \n")
					_world =check_world_input(worlds)
					print("The following dominition relations between rules obtain in " + _world + " (where the left rule dominates the right): \n")
					#temp = int(_world[1:])
					print(worlds[_world].dom)
				elif(com1 == "8"):
					print("The most violated worlds are: \n")
					res = worst_worlds(worlds)
					print(res)
				elif(com1 == "9"):
					print("For which rule would you like to make your query? (type in name) \n")
					for k, rule in rules.items():
						print("%s: %s \n" % (k, rule.item))
					_rule =  check_rule_input(rules)
					print("Body extension of %s is:  %s \n" % (rules[_rule].body, rules[_rule].bodyExtension))
				elif(com1 == "10"):
					print("For which rule would you like to make your query? (type in name) \n")
					for k, rule in rules.items():
						print("%s: %s \n" % (k, rule.item))
					_rule =  check_rule_input(rules)
					print("Head extension of %s is:  %s \n" % (rules[_rule].head, rules[_rule].headExtension))
				elif(com1 == "11"):
					print("For which rule and world are you checking? (write as ri, wi)\n")
					pair = check_rule_world_pair_input(worlds, rules)
					_rule = pair[0]
					_world = pair[1]
					res = dom_of_r_in_w(_rule, _world, rules, worlds)
					_world = re.sub(r"\s+", "", _world)
					_world = int(_world[1:])
					print(_world)
					print("%s is dominated by %s in w%s: %s" % (_rule, res, _world, worlds[_world].state))
				elif(com1 == "12"):
					for world in worlds.values():
						print("%s: %s \n" % (world.name, world.state))
					print("For which rule and world are you checking? (write as ri, wi)\n")
					pair = check_rule_world_pair_input(worlds, rules)
					_rule = pair[0]
					_world = pair[1]
					#_world = re.findall(r'\d+', _world)
					#_world = int(_world[0])
					print("temp: %s, _rule: %s \n" % (_world, _rule))
					if worlds[_world].state in rules[_rule].bodyExtension:
						print("True\n")
						print("%s is in the extension of %s" % (worlds[_world].state, rules[_rule].body))
					else:
						print("False\n")
						print("%s is not in the extension of %s" % (worlds[_world].state, rules[_rule].body))
				elif(com1 == "13"):
					for world in worlds.values():
						print("%s: %s \n" % (world.name, world.state))
					print("For which rule and world are you checking? (write as ri, wi)\n")
					pair = check_rule_world_pair_input(worlds, rules)
					_rule = pair[0]
					_world = pair[1]
					#_world = re.findall(r'\d+', _world)
					#_world = int(_world[0])
					if worlds[_world].state in rules[_rule].headExtension:
						print("True\n")
						print("%s is in the extension of %s" % (worlds[_world].state, rules[_rule].head))
					else:
						print("False\n")
						print("%s is not in the extension of %s" % (worlds[temp].state, rules[_rule].head))
				elif(com1 == "14"):
					print("For which rule would you like to make your query? (type in name) \n")
					for k, rule in rules.items():
						print("%s: %s \n" % (k, rule.item))
					_rule =  check_rule_input(rules)
					print(rules[_rule].body)
				elif(com1 == "15"):
					print("For which rule would you like to make your query? (type in name) \n")
					for k, rule in rules.items():
						print("%s: %s \n" % (k, rule.item))
					_rule =  check_rule_input(rules)
					print(rules[_rule].head)



				else:
					print("I'm sorry, you did not input a recognized command, please try again. \n")
		elif(com == "e"):
			break
		else:
			print("I'm sorry, you did not input a recognized command, please try again. \n")
		more = ""
		while(more != "y" and more != "n"):
			more = input("Would you like to make another query?  (y, n) \n")
			if(more == 'n'):
				break
