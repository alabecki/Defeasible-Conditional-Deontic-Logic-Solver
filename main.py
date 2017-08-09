#/usr/bin/python3
#Naive Preferences Solver _________________________________________________________________________________________________


#Copyright (c) 2017 Adam Labecki

#Permission is hereby granted, free of charge, to any person obtaining a copy
#of this software and associated documentation files (the "Software"), to deal
#in the Software without restriction, including without limitation the rights
#to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
#copies of the Software, and to permit persons to whom the Software is
#furnished to do so, subject to the following conditions:

#The above copyright notice and this permission notice shall be included in all
#copies or substantial portions of the Software.

# For further details see LICENSE 

 #Libraries______________________________________________________________________________________________________________________
from sympy import Symbol
from sympy.abc import*
from sympy.logic.boolalg import to_cnf
from sympy.logic.boolalg import Not, And, Or
from sympy.logic.inference import satisfiable, valid
from mpmath import*
from itertools import product
import sys
from copy import deepcopy
from shutil import copyfile
from itertools import*

import re
from preferences_core_functions import*
from preferences_query_functions import*
from preference_classes import*


commands = {
	"1": "Modal analysis",
	"2": "Inferences from R",
	"3": "Augmenting R",
	"4": "Write Data to text-file",
	"5": "Additional queries",
	"6": "I am done with this file"
}

modal_analysis = {
	"1": "Show the set of most preferable  worlds",
	"2": "Show the set of least preferable worlds",
	"3": "Compare two specific worlds with respect to preference",
	"4": "Show which rules are violated at each world ordered by number of rule violations",
	"5": "Show which rules are violated at each world ordered by weighted number of rule violations",
	"6": "Show the best worlds at which a formula f is true",
	"7": "Return to primary commands"
}

inferences_from_R = {
	"1": "For some a, b, check if R, a |= b holds with respect to obligation",
	"2": "For some a, b, check if R, a |= b holds with respect to permissibility",
	"3": "For some a, b check if R |= (a -> b) obtains", 
	"4": "Generate each instance of R |= (a -> b) for {a, b | a and b are literals obtained from the atoms of R}",
	"5": "Generate all entailments of obligation on R (restricted to literals)",
	"6": "Generate all entailments of permissibility on R (restricted to literals)",
	"7": "Return to primary commands"
}

augmenting_R = {
	"1": "Add a rule to R",
	"2": "Add a constraint to R",
	"3": "Augment current rules with rules from an additional file",
	"4": "Return to primary commands"
}

debugging = {
	"1": "Show the world states at which a given rule is true",
	"2": "Show the world states at which a given rule is violated",
	"3": "Show which rules are false at a given world",
	"4": "Show which rules are verified at a given world",
	"5": "Show which rules are neutral relative to a given world",
	"6": "Show the set of domination relations between rules",
	"7": "Show the body extension of a rule",
	"8": "Show the head extension of a rule",
	"9": "Print body of a rule",
	"10": "Print head of a rule",
	"11": "Show constraints",
	"12": "Show weights of rules",
	"13": "Show dependencies of each world",
	"14": "Return to primary commands"
}

evaluation_method = {
	"1": "By subset relationships in terms of rule violation ",
	"2": "In terms of the cardinality  of rule violations ",
	"3": "In terms of the weighted cardinality of rule violations",
}

save_options = {
	"1": "Save text showing: rule set, constraints, order worlds relative to cardinal preference",
	"2": "Save text showing: rule set, constraints, order worlds relative to weighted cardinal preferences"
}




#Main_____________________________________________________________________________________________________________________
print("\n \n")
print ("~|&->~|&->~|&->~|&->~|&->~|&->~|&->~|&->~|&->~|&->~|&->~|&->~|&->~|&->~|&->~|&->~|&->~|&-> ")
print("_________________________________________________________________________________________\n")
print("                   Welcome to the Defeasible Conditional Logic Solver                     ")
print("__________________________________________________________________________________________ \n")
print ("~|&->~|&->~|&->~|&->~|&->~|&->~|&->~|&->~|&->~|&->~|&->~|&->~|&->~|&->~|&->~|&->~|&->~|&-> \n")

while(True):
	res = base()
	

	file = res[0]
	file_name = res[1]

	print("Processing rules ........................................................ \n")

	files = []
	files.append(file)
	data = initiate(file)

	propositions = data[0]
	rules = data[1]
	constraints = data[2]
	worlds = data[3]

	_continue = True
	while(True):
		print("\n____________________________________________________________________________________ ")
		print("			What would you like to do? 									")
		print("____________________________________________________________________________________ \n")

		for k, v in sorted(commands.items()):
			print("%s: %s " % (k, v))
		com = input()
		if(com == "1"):
			info = "0"
			numlist = list(range(1,8))
			characters = [str(n) for n in numlist]
			while info not in characters:
				print("\n____________________________________________________________________________________ ")
				print("			What would you like to know?")
				print("____________________________________________________________________________________ \n")
				for k, v in sorted(modal_analysis.items()):
					print(k, v)
				print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ \n")
				info = input()
			if info == "1":
				print("\n_______________________________________________________________________________ ")
				print("\n How would you like to evaluate the preference relationship between worlds? \n")
				for k, v in sorted(evaluation_method.items()):
					print(k, v)
				print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ \n")
				method = "0"
				while method != "1" and method != "2" and method != "3":
					method = input()
				if method == "1":
					best_worlds = best_worlds_by_subset(worlds)
					print("\n The most preferred worlds ordered by subsets of violations:")
					print("________________________________________________________________________________ \n")
					for k, v in sorted(best_worlds.items()):
						print("%s: %s, %s \n" % (k, v.state, v.F))
					print("<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><> \n")
				elif method == "2":
					best_worlds = best_worlds_by_cardinality(worlds)
					print("\n The most preferred worlds ordered by number of violated rules: ")
					print("________________________________________________________________________________ \n")
					for k, v in sorted(best_worlds.items()):
						print("%s: %s, %s \n" % (k, v.state, v.F))
				elif method == "3":
					best_worlds = best_worlds_by_weighted_cardinality(worlds)
					print("\nThe most preferred worlds by weighted rule violations: ")
					print("________________________________________________________________________________ \n")
					for k, v in sorted(best_worlds.items()):
						print("%s: %s, %s \n" % (k, v.state, v.F))
				else:
					print("\nThat was not one of the avilable selections, please try again \n")
			elif(info == "2"):
				print("_________________________________________________________________________________ ")
				print("How would you like to evaluate the preference relationship between worlds? \n")
				print("_________________________________________________________________________________ \n")
				for k, v in sorted(evaluation_method.items()):
					print(k, v)
				print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
				method = "0"
				while method != "1" and method != "2" and method != "3":
					method = input()
				if method == "1":
					res = worst_worlds_by_subset(worlds)
					print("The worst worlds are: ")
					print("-----------------------------------------------------------------------------------\n")
					for v in res.values():
						print("%s: %s, %s \n" % (v.name, v.state, v.F))
					print("--------------------------------------------------------------------------------\n")
				elif method == "2":
					res = worst_worlds_by_cardinality(worlds)
					print("The worst worlds are: \n")
					print("-----------------------------------------------------------------------------------\n")
					for v in res.values():
						print("%s: %s, %s \n" % (v.name, v.state, v.F))
					print("---------------------------------------------------------------------------------\n")
				elif method == "3":
					res = worst_worlds_by_weighted_cardinality(worlds)
					print("The worst worlds are: \n")
					print("----------------------------------------------------------------------------------\n")
					for v in res.values():
						print("%s: %s, %s \n" % (v.name, v.state, v.weightedF))
					print("----------------------------------------------------------------------------------\n")
			elif(info == "3"):
				print("_______________________________________________________________________________________ \n")
				print("How would you like to evaluate the preference relationship between worlds? ")
				for k, v in sorted(evaluation_method.items()):
					print(k, v)
				print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
				method = "0"
				while method != "1" and method != "2" and method != "3":
					method = input()
				for world in worlds.values():
					print("%s: %s \n" % (world.name, world.state))
				check = [False, False]
				while check[0] == False or check[1] == False:
					_pair = input("which two worlds would you like to compare? (write: 'wi, wj', where i, j are integers) ")
					print("_________________________________________________________________________________________________ \n")
					pair = _pair.split(",")
					if "," not in _pair:
						print("The input is not in the right format, please try again")
						continue
					check[0] = check_world_input2(pair[0], worlds)
					check[1] = check_world_input2(pair[1], worlds)
					if check[0] == False or check[1] == False:
						print("The input did not conist of two worlds seperated by a comma, please try again")
						continue

				if method == "1":
					compare_worlds_by_subset(pair[0], pair[1], worlds)
				if method == "2":
					compare_worlds_by_cardinality(pair[0], pair[1], worlds)
				if method == "3":
					compare_worlds_by_weighted_cardinality(pair[0], pair[1], worlds)

			elif info == "4":
				print("__________________________________________________________________________________ \n")
				print("Worlds ordered by cardinality of rule violation:")
				print("__________________________________________________________________________________ \n")
				print_worlds_by_cardinality(worlds)

			elif info == "5":
				print("__________________________________________________________________________________ \n")
				print("Worlds ordered by weighted cardinality of rule violation: ")
				print("__________________________________________________________________________________ \n")
				print_worlds_by_weighed_cardinality(worlds)

			elif(info == "6"):
				print("_____________________________________________________________________________________")
				formula = input("Please write a formula to check ")
				print("_____________________________________________________________________________________")
				formula_ext = assign_extensions(formula, worlds, propositions)
				print("_____________________________________________________________________________________")
				print("How would you like to evaluate the preference relationship between worlds? ")
				print("_____________________________________________________________________________________")

				for k, v in sorted(evaluation_method.items()):
					print(k, v)
				print("-----------------------------------------------------------------------------------\n")
				method = "0"
				while method != "1" and method != "2" and method != "3":
					method = input()
				if method == "1":
					formula_min = get_min_F_subset(formula_ext, worlds)
					print(" The best %s-worlds are: " % (formula))
					print("----------------------------------------------------------------------------------\n")
					for w in formula_min:
						print (w.name, w.state, w.F)
					print("\n")
				if method == "2":
					formula_min = get_min_F_card(formula_ext, worlds)
					print(" The best %s-worlds are: " % (formula))
					print("----------------------------------------------------------------------------------\n")
					for w in formula_min:
						print (w.name, w.state, w.F)
						print("\n")
				if method == "3":
					formula_min = get_min_F_weight(formula_ext, worlds)
					print(" The best %s-worlds are: " % (formula))
					print("----------------------------------------------------------------------------------\n")
					for w in formula_min:
						print (w.name, w.state, w.weightedF)
					print("\n")
				else:
					print("Please select one of the following options...")
			elif info == "7":
				print("... \n")
			else:
				print("Please select one of the following options...")

		elif(com == "2"):
			print("\n_____________________________________________________________________________________ ")
			print("			What would you like to check?								")
			print("_______________________________________________________________________________________ \n")
			#for k, v in inferences_from_R.items():
			#	print(k, v)
			#print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ \n")
			infer = "0"
			while infer not in inferences_from_R.keys():
				for k, v in sorted(inferences_from_R.items()):
					print(k, v)
				print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ \n")
				infer = input()
				if infer not in inferences_from_R.items():
					print("That was not one of the options. Please try again \n")
			if infer == "1":
				print("__________________________________________________________________________________ \n")
				p = input("Please enter the first formula using &, ~, and | as operators \n")
				print("__________________________________________________________________________________ \n")
				q = input("Please enter the second formula using &, ~, and | as operators \n")
				print("__________________________________________________________________________________ \n")
				current_num_proposition = len(propositions)
				propositions2 = deepcopy(propositions)
				add_proposition(propositions2, p)
				add_proposition(propositions2, q)
				print("How would you like to evaluate the preference relationship between worlds? ")
				for k, v in sorted(evaluation_method.items()):
					print(k, v)
				print("------------------------------------------------------------------------------")
				method = "0"
				while method != "1" and method != "2" and method != "3":
					method = input()
				if len(propositions2) == current_num_proposition:
					p_ext = assign_extensions(p, worlds, propositions)
					if method == "1":
						p_min = get_min_F_subset(p_ext, worlds)
					if method == "2":
						p_min = get_min_F_card(p_ext, worlds)
					if method == "3":
						p_min = get_min_F_weight(p_ext, worlds)
					q_ext = assign_extensions(q, worlds, propositions)
					b = obligation_implication(p_min, q_ext, worlds)
					if b == True:
						print("Given our preferences, %s entails that %s is obligatory\n" % (p, q))
						print("________________________________________________________\n")
					if b == False:
						print("Given our preferences, %s does not entail that %s is obligatory \n" % (p, q))
						print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ \n")
				else:
					worlds_extended = reconstruct_worlds(propositions2, constraints)
					rules2 = deepcopy(rules)
					for k, rule in rules2.items():
						rule.bodyExtension = assign_extensions(rule.body, worlds_extended, propositions2)
						rule.headExtension = assign_extensions(rule.head, worlds_extended, propositions2)
					domination_relations(rules2)
					assign_rule_violations(worlds_extended, rules2)
					p_ext = assign_extensions(p, worlds_extended, propositions2)
					if method == "1":
						p_min = get_min_F_subset(p_ext, worlds)
					if method == "2":
						p_min = get_min_F_card(p_ext, worlds)
					if method == "3":
						p_min_ = get_min_F_weight(p_ext, worlds)
					q_ext = assign_extensions(q, worlds_extended, propositions2)
					b = obligation_implication(p_min, q_ext, worlds_extended)
					if b == True:
						print("Given our preferences, %s entails that %s is obligatory\n" % (p, q))
						print("________________________________________________________\n")
					if b == False:
						print("Given our preferences, %s does not entail that %s is obligatory \n" % (p, q))
						print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ \n")

			elif(infer == "2"):
				print("__________________________________________________________________________________ \n")
				p = input("Please enter the first formula using &, ~, and | as operators \n")
				print("__________________________________________________________________________________ \n")
				q = input("Please enter the second formula using &, ~, and | as operators \n")
				print("__________________________________________________________________________________ \n")
				current_num_proposition = len(propositions)
				propositions2 = deepcopy(propositions)
				add_proposition(propositions2, p)
				add_proposition(propositions2, q)
				print("How would you like to evaluate the preference relationship between worlds? ")
				for k, v in sorted(evaluation_method.items()):
					print(k, v)
				print("--------------------------------------------------------------------------------\n")
				method = "0"
				while method != "1" and method != "2" and method != "3":
					method = input()

				if len(propositions2) == current_num_proposition:
					p_ext = assign_extensions(p, worlds, propositions)
					if method == "1":
						p_min = get_min_F_subset(p_ext, worlds)
					if method == "2":
						p_min = get_min_F_card(p_ext, worlds)
					if method == "3":
						p_min_ = get_min_F_weight(p_ext, worlds)
					q_ext = assign_extensions(q, worlds, propositions)
					b = permissable_implication(p_min, q_ext, worlds)
					if b == True:
						print("Given our preferences, %s entails that %s is permissible \n" % (p, q))
						print("________________________________________________________ \n")
					if b == False:
						print("Given our preferences, %s does not entail that %s is permissible \n" % (p, q))
						print("________________________________________________________________ \n")
				else:
					worlds_extended = reconstruct_worlds(propositions2, constraints)
					rules2 = deepcopy(rules)
					for k, rule in rules2.items():
						rule.bodyExtension = assign_extensions(rule.body, worlds_extended, propositions2)
						rule.headExtension = assign_extensions(rule.head, worlds_extended, propositions2)
					domination_relations(rules2)
					assign_rule_violations(worlds_extended, rules2)
					p_ext = assign_extensions(p, worlds, propositions)

					if method == "1":
						p_min = get_min_F_subset(p_ext, worlds)
					if method == "2":
						p_min = get_min_F_card(p_ext, worlds)
					if method == "3":
						p_min_ = get_min_F_weight(p_ext, worlds)
					q_ext = assign_extensions(q, worlds_extended, propositions2)
					b = permissable_implication(p_min, q_ext, worlds_extended)
					if b == True:
						print("Given our preferences, %s entails that %s is permissible " % (p, q))
						print("________________________________________________________ \n")
					if b == False:
						print("Given our preferences, %s does not entail that %s is permissible \n" % (p, q))
						print("_________________________________________________________________ \n")

			elif(infer == "3"):
				print("->->->->->->->->->->->->->->->->->->->->->->->->->->->->->->->->->->->->\n")
				r = input("Please enter a new rule in the same format as in the txt. file ")
				print("__________________________________________________________________________________ \n")
				current_num_proposition = len(propositions)
				propositions2 = deepcopy(propositions)
				add_proposition(propositions2, r)
				if len(propositions2) == current_num_proposition:
					rules2 = deepcopy(rules)
					worlds2 = reconstruct_worlds(propositions, constraints)
					if implicit_rule(r, worlds, worlds2, propositions, rules2) == True:
						print("Yes, %s is implied by the other rules \n" % (r))
						print("***************************************** \n")
					else:
						print("No, %s is not implied by the other rules \n" % (r))
						print("***************************************** \n")
				else:
					worlds_extended = reconstruct_worlds(propositions2, constraints)
					worlds2 = reconstruct_worlds(propositions2, constraints)
					for k, rule in rules.items():
						rule.bodyExtension = assign_extensions(rule.body, worlds_extended, propositions2)
						rule.headExtension = assign_extensions(rule.head, worlds_extended, propositions2)
					assign_rule_violations(worlds_extended, rules)
					rules2 = deepcopy(rules)
					#if(len(propositions > current_num_proposition)):
					if implicit_rule(r, worlds_extended, worlds2, propositions2, rules2) == True:
						print("Yes, %s is implied by the other rules \n" % (r))
						print("**************************************** \n")

					else:
						print("No, %s is not implied by the other rules \n" % (r))
						print("******************************************* \n")

			elif(infer == "4"):
				print("Would you like propositions to freely occur in both the head and body of the rules or \
					should they be restricted to the roles that they play in the ruleset? \n")
				print("1: Let propositions found in rules freely occur as both conditions (body) and obligations (head)")
				print("2: Restrict propositions to the roles they play in the rules")
				prop = input()
				#props = deepcopy(propositions)
				if prop == "1":
					domain = free_generate_prop_product(propositions, rules, constraints)
				if prop == "2":
					domain = restricted_generate_prop_product(propositions, rules, constraints)
				print("|- |- |- |- |- |- |- |- |- |- |- |- |- |- |- |- |- |- |- |- |- |- |- |- |- |- |-  \n")
				print("Calculating implicit rules: \n")
				D = []
				for d in domain:
					temp1 = list(d)
					
					if strip_not(str(temp1[0])) == strip_not(str(temp1[1])):
						continue
					temp2 = "(" + str(temp1[0]) + "->" + str(temp1[1]) + ")"
					
					D.append(temp2)
				
				items = []
				for r, rule in rules.items():
					thing = rule.body + "->" + rule.head
					items.append(thing)

				for d in D:
					_d = from_prefix(d)
					rules2 = deepcopy(rules)
					
					worlds2 = reconstruct_worlds(propositions, constraints)
					if implicit_rule(_d, worlds, worlds2, propositions, rules2) == True:
					
						check = _d.replace("(", "")
						check = check.replace(")", "")
						#print("Check:  %s " % (_d))
						if check in items:
							continue
						else:
							add_rule(_d, rules)

				for k, rule in rules.items():
					rule.bodyExtension = assign_extensions(rule.body, worlds, propositions)
					rule.headExtension = assign_extensions(rule.head, worlds, propositions)
				domination_relations(rules)
				assign_rule_violations(worlds, rules)
				print("R now consists of the following: ")
				for r, rule in sorted(rules.items()):
					print(r, rule.item)
				print("-------------------------------------------------------------------- \n")
		

			elif (infer == "5"):
				print("Would you like propositions to freely occur in both the head and body of the rules or \
					should they be restricted to the roles that they play in the ruleset? \n")
				print("1: Let propositions found in rules freely occur as both conditions (body) and obligations (head)")
				print("2: Restrict propositions to the roles they play in the rules")
				prop = input()
				#props = deepcopy(propositions)
				if prop == "1":
					domain = free_generate_prop_product(propositions, rules, constraints)
				if prop == "2":
					domain = restricted_generate_prop_product(propositions, rules, constraints)
				print("|= |= |= |= |= |=|= |= |=|= |= |=|= |= |=|= |= |=|= |= |=|= |= |=|= |= |=|= |= |= \n")
				print("Calculating Literal Entailments of Obligation on R: \n")
				for d in domain:
					#print("d[0]: %s" % (d[0]))
					#print("d[1]: %s" % (d[1]))
					res = set_up_implications(d, worlds, propositions)
					if res == "nil":
						continue
					t1min = res[0]
					t2ext = res[1]
					a = res[2]
					b = res[3]
		
					if obligation_implication(t1min, t2ext, worlds) == True:
						print("%s |= %s" % (a, b))
				print("\n")

			elif (infer == "6"):
				print("Would you like propositions to freely occur in both the head and body of the rules or \
					should they be restricted to the roles that they play in the ruleset? \n")
				print("1: Let propositions found in rules freely occur as both conditions (body) and obligations (head)")
				print("2: Restrict propositions to the roles they play in the rules")
				prop = input()
				if prop == "1":
					domain = free_generate_prop_product(propositions, rules, constraints)
				if prop == "2":
					domain = restricted_generate_prop_product(propositions, rules, constraints)
				print("|= |= |= |= |= |=|= |= |=|= |= |=|= |= |=|= |= |=|= |= |=|= |= |=|= |= |=|= |= |= \n")
				print("Calculating Literal Entailments of Permissibility on R: \n")
				for d in domain:
					res = set_up_implications(d, worlds, propositions)
					if res == "nil":
						continue
					t1min = res[0]
					t2ext = res[1]
					a = res[2]
					b = res[3]
					#print(t2ext)
					if permissable_implication(t1min, t2ext, worlds) == True:
						print("%s |= %s" % (a, b))

			if infer == "7":
				print("... \n")
						

		elif(com == "3"):
			print("\n____________________________________________________________________________ ")
			print("			How would you like to augment R?							")
			print("______________________________________________________________________________ \n")
			#for k, v in augmenting_R.items():
			#	print(k, v)
			#print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ \n")
			add = "0"
			while add not in augmenting_R.keys():
				for k, v in sorted(augmenting_R.items()):
					print(k, v)
				print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ \n")
				add = input()
				if add not in augmenting_R:
					print("%s is not one of the options. Please try again \n" % (add))
			if add == "1":
				print("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ \n")
				new_rule = input("Please input a new rule in the same format as used in the txt. file \n")
				add_proposition(propositions, new_rule)
				add_rule(new_rule, rules)
				worlds = reconstruct_worlds(propositions, constraints)
				for k, rule in rules.items():
					#print(k, rule.item)
					rule.bodyExtension = assign_extensions(rule.body, worlds, propositions)
					rule.headExtension = assign_extensions(rule.head, worlds, propositions)
				domination_relations(rules)
				assign_rule_violations(worlds, rules)
				print("The new rule has been added to R ")
				print("R now consists of the following: ")
				for r, rule in sorted(rules.items()):
					print(r, rule.item)
				print("---------------------------------------------------------- \n")

			if add == "2":
				print("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ \n")
				constraint = input("Please input a new constraint as an atomic formual (do not include the '!') \n")
				add_constraint(constraint, constraints)
				add_proposition(propositions, constraint)
				worlds = reconstruct_worlds(propositions, constraints)
				for k, rule in rules.items():
					#print(k, rule.item)
					rule.bodyExtension = assign_extensions(rule.body, worlds, propositions)
					rule.headExtension = assign_extensions(rule.head, worlds, propositions)
				domination_relations(rules)
				assign_rule_violations(worlds, rules)
				print("The new constraint has been added to R ")
				print("R now consists of the following constraints: ")
				for k, v in sorted(constraints.items()):
					print(k, v.item)
				print("---------------------------------------------------------- \n")


			if add == "3":
				print("txt.txt.txt.txt.txt.txt.txt.txt.txt.txt.txt.txt.txt.txt.txt.txt.txt.txt.txt.txt. \n")
				#copyfile("filename", "temp.txt")
				combined_file = open("temp2.txt", 'a+')
				files.append(combined_file)
				delete_file_content(combined_file)
				file.seek(0)
				for line in file:
					buf = line
					combined_file.write("%s\n" % (buf))
				print("Please input the name of a text-file containing a set of rules ")
				print("(or press 'r' to return) \n")
				name = input()
				if name != "r":
					_new_file = get_file(name)
					new_file = _new_file[0]
					new_file_name = _new_file[1]
					for line in new_file:
						buf = line
						combined_file.write("%s\n" % (buf))
					new_file.close()
					combined_file.close()
					combined_file = open("temp2.txt", 'r+')
					#for line in combined_file:
						#print(line)
					combined_file.seek(0)

					data = initiate(combined_file)

					propositions = data[0]
					rules = data[1]
					constraints = data[2]
					worlds = data[3]

					print("The new rules have been merged with the old ones\n ")
					print("&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_ \n")
					print("R now consists of the following: ")
					for r, rule in sorted(rules.items()):
						print(r, rule.item)
					print("---------------------------------------------------------- \n")
			if add == "4":
				print("... \n")

		elif(com == "5"):
			print("\n__________________________________________________________________________________ \n")
			print("			What else would you like to know?							")
			print("__________________________________________________________________________________ \n")
			com1 = " "
			choices = list(range(1, 15))
			char = [str(n) for n in choices]
			orders = sorted(list(debugging.keys()))
			while (com1 not in char):
				for i in range(1, len(orders) + 1):
					print(i, debugging[str(i)])
				#for k, v in sorted(debugging.items()):
				#	print("%s: %s \n" % (k, v))
				com1 = input()
			if com1 == "1":
				print("For which rule would you like to make your query? (type in name) ")
				print("------------------------------------------------------------------ \n")
				for k, rule in sorted(rules.items()):
					print("%s: %s \n" % (k, rule.item))
				_rule =  check_rule_input(rules)
				result = find_rule_extension(_rule, rules, worlds)
				print("%s is true in the following worlds:\n" % (_rule))
				for w in result:
					print(w)

			elif(com1 == "2"):
				print("For which rule would you like to make your query? (type in name) ")
				print("------------------------------------------------------------------ \n")
				for k, rule in sorted(rules.items()):
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
				print("\n")
				for w in worlds.values():
					item = print_false_rules_at_w(w.name, rules, worlds)
					print(w.state, item)
				print("<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><> \n")

			elif(com1 == "4"):
				print("For which world would you like to make your query?")
				for world in worlds.values():
					print("%s: %s \n" % (world.name, world.state))
				print("________________________________________________________________ \n")
				print("For which world would you like to make your query? (type in name) \n")
				_world =check_world_input(worlds)
				result = print_rules_true_at_w(_world, rules, worlds)
				print("The following rules are true in " + _world + ":")
				print(result)
				print("<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><> \n")

			elif(com1 == "5"):
				print("For which world would you like to make your query?")
				for world in worlds.values():
					print("%s: %s \n" % (world.name, world.state))
				print("For which world would you like to make your query? (type in name) \n")
				_world =check_world_input(worlds)
				result = print_rules_neutral_at_w(_world, rules, worlds)
				print("The following rules are neutral in " + _world + ":")
				print(result)
				print("<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><> \n")

			elif(com1 == "6"):
				print("The following domination relations obtain: " )
				print("__________________________________________ \n")
				for rule in rules.values():
					if (len(rule.dominatedBy) != 0):
						print("%s is dominated by: " % (rule.name))
						for dom in rule.dominatedBy:
							print(dom.name)
				print("<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><> \n")

			elif(com1 == "7"):
				print("For which rule would you like to make your query? (type in name) \n")
				for k, rule in sorted(rules.items()):
					print("%s: %s \n" % (k, rule.item))
				_rule =  check_rule_input(rules)
				print("Body extension of %s is:  %s \n" % (rules[_rule].body, rules[_rule].bodyExtension))

			elif(com1 == "8"):
				print("For which rule would you like to make your query? (type in name) \n")
				for k, rule in sorted(rules.items()):
					print("%s: %s \n" % (k, rule.item))
				_rule =  check_rule_input(rules)
				print("Head extension of %s is:  %s \n" % (rules[_rule].head, rules[_rule].headExtension))

			elif(com1 == "9"):
				print("For which rule would you like to make your query? (type in name) \n")
				for k, rule in sorted(rules.items()):
					print("%s: %s \n" % (k, rule.item))
				_rule =  check_rule_input(rules)
				print(rules[_rule].body)
			elif(com1 == "10"):
				print("For which rule would you like to make your query? (type in name) \n")
				for k, rule in sorted(rules.items()):
					print("%s: %s \n" % (k, rule.item))
				_rule =  check_rule_input(rules)
				print(rules[_rule].head)

			elif(com1 == "11"):
				for k, v in sorted(constraints.items()):
					print(v.name, v.item)

			elif (com1 == "12"):
				for rule in rules.values():
					print("%s: %s - %s \n" % (rule.name, rule.item, rule.weight) )

			elif (com1 == "13"):
				for w, world in sorted(worlds.items()):
					print("World: %s \n" %  (world.name))
					for d in world.dependency:
						print(d.name, end=' ')
			elif (com1 == "14"):
				print("...\n")
			else:
				print("I'm sorry, you did not input a recognized command, please try again. \n")	
		
		elif(com == "4"):
			print(" txt.txt.txt.txt.txt.txt.txt.txt.txt.txt.txt.txt.txt.txt.txt.txt.txt.txt.txt.txt.txt.\n")
			text_name = input("Please provide a name for the text file (not including file extension)...\n ")
			print("__________________________________________________________________________________ \n")
			text_name = text_name + ".txt"
			save = open(text_name, 'a+')
			save.write("Defeasable Conditional Deontic Logic Results")
			save.write("____________________________________________ \n \n")

			save.write("Rules: \n")
			for r, rule in sorted(rules.items()):
				line = r + " " + rule.item
				save.write("%s\n" % (line))
			save.write("\n")
			save.write("Constraints: \n")
			for c, con in sorted(constraints.items()):
				line = c + " " + con.item
				save.write("%s\n" % (line))
			save.write("\n")

			print("Please select one of the following:")
			print("___________________________________ ")
			for k, v in sorted(save_options.items()):
				print (k, v)
			print("<><><><><><><><><><><><><><><><><><><><><><><><>")

			selection = input()
			save.write("Sorted worlds with their rule violations: \n")
			if selection == "1":
				sorted_worlds = sorted(worlds.values(), key =lambda x: len(x.F))
				for i in sorted_worlds:
					save.write("%s: %s, %s, %s \n" % (i.name, i.state, i.F, i.weightedF))
			if selection == "2":
				sorted_worlds = sorted(worlds.values(), key =lambda x: x.weightedF)
				for i in sorted_worlds:
					save.write("%s: %s, %s, %s \n" % (i.name, i.state, i.F, i.weightedF))
				save.write("%s \n" % ("\n"))

			while True:
				print("~|&~|&~|&~|&~|&~|&~|&~|&~|&~|&~|&~|&~|&~|&~|&~|&~|&~|&~|&~|&~|&~|&~|&~|&~|&~|&~|&~|&~|&~|& \n")
				more = input("Would you like to augment your file with the best f worlds, for some formula f? (y/n) \n")
				print("--------------------------------------------------------------------------------------------- \n")
				if more == "n":
					save.close()
					print("%s has been written to your directory " % (text_name))
					print("<><><><><><><><><><><><><><><><><><><> \n")
					break
				if more == "y":
					formula = input("Please write a formula to check \n")
					formula_ext = assign_extensions(formula, worlds, propositions)
					save.write("The best %s-worlds: \n \n" % (formula))
					print("How would you like to evaluate the preference relationship between worlds? ")
					print("__________________________________________________________________________ ")
					for k, v in sorted(evaluation_method.items()):
						print(k, v)
					print("\n")
					method = input()
					if method == "1":
						formula_min = get_min_F_subset(formula_ext, worlds)
					if method == "2":
						formula_min = get_min_F_card(formula_ext, worlds)
					if method == "3":
						formula_min = get_min_F_weight(formula_ext, worlds)
					for w in formula_min:
						save.write("%s: %s, %s \n" % (w.name, w.state, w.F))
					save.write("\n")
				else:
					print("Please input either 'y' or 'n' ")
					print("<><><><><><><><><><><><><><><> ")


		elif(com == "6"):
			print(" <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<\n")
			print("The file has been closed. ")
			print(" >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>> \n")

			for f in files:
				f.close()
			break
		else:
			print("I'm sorry, you did not input a recognized command, please try again. ")
			print(".....")

		#more = ""
		#while(more != "y" and more != "n"):
		#	more = input("Would you like to make another query?  (y, n) \n")
		#	print("____________________________________________________ \n")
		#if(more == 'n'):
		#	for f in files:
		#		f.close()
		#	break
