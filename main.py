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
from sympy.logic.inference import satisfiable, valid
from mpmath import*
from itertools import product
import sys
from copy import deepcopy
from shutil import copyfile

import re
from preferences_core_functions import*
from preferences_query_functions import*
from preference_classes import*



commands = {
	"1": "Show the set of most preferable  worlds",
	"2": "Show the set of least preferable worlds",
	"3": "Compare two specific worlds with resepect to preference",
	"4": "Show which rules are violated at each world ordered by number of rule violations",
	"5": "Show which rules are violated at each world ordered by weighted number of rule violations",
	"6": "Show the best worlds at which a formula f is true",
	"7": "Determine whether, given R, the truth of 'a' makes 'b' obligatory (user povides a and b)",
	"8": "Determine whether, given R, the truth 'a' makes 'b' permissible (user provides a and b)",
	"9": "Determine whether, given our preferences, a further rule is implied (user provides new rule (a, b))",
	"10": "Add rule to R",
	"11": "Augment current rules with rules from an additional file",
	"12": "Additional Queries",
	"13": "Write data to text-file",
	"14": "I am done with this file"
}

debugging = {
	"1": "Show the world states at which a given rule is true",
	"2": "Show the world states at which a given rule is violated",
	"3": "Show which rules are false at a given world",
	"4": "Show which rules are verified  at a given world",
	"5": "Show which rules are neutral relative to a given world",
	"6": "Show the set of domination relations between rules",
	"7": "Show the body extension of a rule",
	"8": "Show the head extension of a rule",
	"9": "Print body of a rule",
	"10": "Print head of a rule",
	"11": "Show constraints",
	"12": "Show weights of rules",
	"13": "Show dependencies of each world"
}


evaluation_method = {
	"1": "By subset relationships in terms of rule violation \n",
	"2": "In terms of the cadinality of rule violations \n",
	"3": "In terms of the weighted cardinality of rule violations \n"
}


save_options = {
	"1": "Save text showing essential data: rule set, constraints, list of worlds with the rules they violate in order of cardinal preference",

}

#Main_____________________________________________________________________________________________________________________


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
			res = get_file()
			file = res[0]
			file_name = res[1]
		else:
			print("I'm sorry, could you repeat your command? \n")

	print("Processing rules____________________________________________________________ \n")

	data = initiate(file)

	propositions = data[0]
	rules = data[1]
	constraints = data[2]
	worlds = data[3]

	_continue = True

	while(True):

		print("________________________________________________________________________________ \n")
		print(" What would you like to know? \n")

		for k, v in commands.items():
			print("%s: %s \n" % (k, v))
		com = input()
		if(com == "1"):
			print("How would you like to evaulate the preference relationship between worlds? \n")
			for k, v in evaluation_method.items():
				print(k, v)
			print("\n")
			method = input()
			if method == "1":
				best_worlds = best_worlds_by_subset(worlds)
			if method == "2":
				best_worlds = best_worlds_by_cardinality(worlds)
			if method == "3":
				best_worlds = best_worlds_by_weighted_cardinality(worlds)
			print(" The most preferred worlds are: \n")
			for k, v in best_worlds.items():
				print("%s: %s \n" % (k, v.state))
		elif(com == "2"):
			print("How would you like to evaulate the preference relationship between worlds? \n")
			for k, v in evaluation_method.items():
				print(k, v)
			print("\n")
			method = input()
			if method == "1":
				res = worst_worlds_by_subset(worlds)
				print("The worst worlds are: \n")
				for v in res.values():
					print("%s: %s \n" % (v.name, v.F))
			elif method == "2":
				res = worst_worlds_by_cardinality(worlds)
				print("The worst worlds are: \n")
				for v in res.values():
					print("%s: %s \n" % (v.name, v.F))
			elif method == "3":
				res = worst_worlds_by_weighted_cardinality(worlds)
				print("The worst worlds are: \n")
				for v in res.values():
					print("%s: %s \n" % (v.name, v.weightedF))
		elif(com == "3"):
			print("How would you like to evaulate the preference relationship between worlds? \n")
			for k, v in evaluation_method.items():
				print(k, v)
			method = input()
			print("Which two worlds would you like to compare? \n")
			for world in worlds.values():
				print("%s: %s \n" % (world.name, world.state))
			_pair = input("which two worlds would you like to compare? (write as: 'wi, wj', where i, j are integers) \n")
			pair = _pair.split(",")
			if method == "1":
				compare_worlds_by_subset(pair[0], pair[1], worlds)
			if method == "2":
				compare_worlds_by_cardinality(pair[0], pair[1], worlds)
			if method == "3":
				compare_worlds_by_weighted_cardinality(pair[0], pair[1], worlds)

		elif com == "4":
			print("How would you like to evaulate the preference relationship between worlds? \n")
			for k, v in evaluation_method.items():
				print(k, v)
			method = input()
			if method == "1":
				print("The worlds ordered to partial subset order \n")
				print_worlds_by_partial_order(worlds)
			elif method == "2":
				print("The worlds ordered by cardinality of rule violation: \n")
				print_worlds_by_cardinality(worlds)
			elif method == "3":
				print("The worlds ordered by weighted cardinality of rule violation \n")
				print_worlds_by_weighed_cardinality(worlds)


		elif(com == "6"):
			formula = input("Please write a formula to check \n")
			formula_ext = assign_extensions(formula, worlds, propositions)
			print("How would you like to evaulate the preference relationship between worlds? \n")
			for k, v in evaluation_method.items():
				print(k, v)
			print("\n")
			method = input()
			if method == "1":
				formula_min = get_min_F_subset(formula_ext, worlds)
				print(" The best %s-worlds are: \n" % (formula))
				for w in formula_min:
					print (w.name, w.state, w.F)
				print("\n")
			if method == "2":
				formula_min = get_min_F_card(formula_ext, worlds)
				print(" The best %s-worlds are: \n" % (formula))
				for w in formula_min:
					print (w.name, w.state, w.F)
					print("\n")
			if method == "3":
				formula_min = get_min_F_weight(formula_ext, worlds)
				print(" The best %s-worlds are: \n" % (formula))
				for w in formula_min:
					print (w.name, w.state, w.weightedF)
				print("\n")


		elif(com == "7"):
			p = input("Please enter the first formula using &, ~, and | as operators \n")
			q = input("Please enter the second fomula using &, ~, and | as operators \n")
			current_num_proposition = len(propositions)
			propositions2 = deepcopy(propositions)
			add_proposition(propositions2, p)
			add_proposition(propositions2, q)
			print("How would you like to evaulate the preference relationship between worlds? \n")
			for k, v in evaluation_method.items():
				print(k, v)
			print("\n")
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
				b = obligation_implication(p_min, q_ext, worlds)
				if b == True:
					print("Given our preferences, %s obgliates %s \n" % (p, q))
				if b == False:
					print("Given our preferences, %s does not obligate %s \n" % (p, q))

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
					print("Given our preferences, %s obgliates %s \n" % (p, q))
				if b == False:
					print("Given our preferences, %s does not obligate %s \n" % (p, q))

		elif(com == "8"):
			p = input("Please enter the first formula using &, ~, and | as operators \n")
			q = input("Please enter the second fomula using &, ~, and | as operators \n")
			current_num_proposition = len(propositions)
			propositions2 = deepcopy(propositions)
			add_proposition(propositions2, p)
			add_proposition(propositions2, q)
			print("How would you like to evaulate the preference relationship between worlds? \n")
			for k, v in evaluation_method.items():
				print(k, v)
			print("\n")
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
					print("Given our preferences, %s is permissable, given %s  \n" % (q, p))
				if b == False:
					print("Given our preferences, %s is not permissible, given %s \n" % (q, p))

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
					print("Given our preferences, %s is permissable, given %s  \n" % (q, p))
				if b == False:
					print("Given our preferences, %s is not permissible, given %s \n" % (q, p))

		elif(com == "9"):
			r = input("Please enter a new rule in the same format as in the txt. file \n")
			current_num_proposition = len(propositions)
			propositions2 = deepcopy(propositions)
			add_proposition(propositions2, r)
			if len(propositions2) == current_num_proposition:
				rules2 = deepcopy(rules)
				worlds2 = reconstruct_worlds(propositions, constraints)
				if implicit_rule(r, worlds, worlds2, propositions, rules2) == True:
					print("Yes, %s is implied by the other rules \n" % (r))
				else:
					print("No, %s is not implied by the other rules \n" % (r))
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
				else:
					print("No, %s is not implied by the other rules \n" % (r))

		elif(com == "10"):
			new_rule = input("Please input a new rule in the same format as used in the txt. file \n")
			add_proposition(propositions, new_rule)
			worlds = reconstruct_worlds(propositions, constraints)
			add_rule(new_rule, rules)
			for k, rule in rules.items():
				print(k, rule.item)
				rule.bodyExtension = assign_extensions(rule.body, worlds, propositions)
				rule.headExtension = assign_extensions(rule.head, worlds, propositions)
			domination_relations(rules)
			assign_rule_violations(worlds, rules)

		elif(com == "11"):
			#copyfile("filename", "temp.txt")

			combined_file = open("temp2.txt", 'a+')
			delete_file_content(combined_file)
			file.seek(0)
			for line in file:
				print("What the fuck is your problem?")
				buf = line
				print("Print buf: %s \n" % (buf))
				combined_file.write("%s\n" % (buf))
			_new_file = get_file()
			new_file = _new_file[0]
			new_file_name = _new_file[1]
			for line in new_file:
				buf = line
				print("Print buf: %s \n" % (buf))
				combined_file.write("%s\n" % (buf))
			combined_file.close()
			combined_file = open("temp2.txt", 'r+')
			print("Combined File")
			for line in combined_file:
				print(line)
			combined_file.seek(0)

			#filenames = [  temp + '.tx',  new_file + '.txt', ...]
			#with open('path/to/output/file', 'w') as outfile:
    		#for fname in filenames:
        		#with open(fname) as infile:
            	#outfile.write(infile.read())


			#for v in rules.values():
				#new_line = v.item

			#	new_file.write("%s\n" % (new_line))
				#new_file.writelines(new_line)
			#for line in new_file:
				#print (line)
		#	for c in constraints.values():
			#	new_line = "!" + c.item
				#new_file.writeline("%s\n" % (new_line))
			#new_file.seek(0)
			data = initiate(combined_file)

			propositions = data[0]
			rules = data[1]
			constraints = data[2]
			worlds = data[3]

			#new_propositions = obtain_atomic_formulas(new_file)
			#propositions = propositions | new_propositions
			#new_file.seek(0)
			#add_rules_from_file(new_file, rules)
			#new_file.seek(0)
			#add_constraints_from_file(new_file, constraints)
			#worlds = reconstruct_worlds(propositions,constraints)
			#for k, rule in rules.items():
			#	rule.bodyExtension = assign_extensions(rule.body, worlds, propositions)
			#	rule.headExtension = assign_extensions(rule.head, worlds, propositions)
			#domination_relations(rules)
			#assign_rule_violations(worlds, rules)
			print("The new rules have been merged with the old ones \n")

		elif(com == "12"):
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
					print("The following worlds violate the following rules: \n")
					for world in worlds.values():
						print("%s %s: %s \n" % (world.name, world.state, world.F))

				elif(com1 == "4"):
					print("\n")
					for w in worlds.values():
						item = print_false_rules_at_w(w.name, rules, worlds)
						print(w.state, item)

				elif(com1 == "4"):
					print("For which world would you like to make your query?")
					for world in worlds.values():
						print("%s: %s \n" % (world.name, world.state))
					print("For which world would you like to make your query? (type in name) \n")
					_world =check_world_input(worlds)
					result = print_rules_true_at_w(_world, rules, worlds)
					print("The following rules are true in " + _world)
					print(result)

				elif(com1 == "5"):
					print("For which world would you like to make your query?")
					for world in worlds.values():
						print("%s: %s \n" % (world.name, world.state))
					print("For which world would you like to make your query? (type in name) \n")
					_world =check_world_input(worlds)
					result = print_rules_neutral_at_w(_world, rules, worlds)
					print("The following rules are neutral in " + _world)
					print(result)

				elif(com1 == "6"):
					print("The following domination relations obtain: \n" )
					for rule in rules.values():
						if (len(rule.dominatedBy) != 0):
							print("%s is dominated by: " % (rule.name))
							for dom in rule.dominatedBy:
								print(dom.name)


				elif(com1 == "7"):
					print("For which rule would you like to make your query? (type in name) \n")
					for k, rule in rules.items():
						print("%s: %s \n" % (k, rule.item))
					_rule =  check_rule_input(rules)
					print("Body extension of %s is:  %s \n" % (rules[_rule].body, rules[_rule].bodyExtension))
				elif(com1 == "8"):
					print("For which rule would you like to make your query? (type in name) \n")
					for k, rule in rules.items():
						print("%s: %s \n" % (k, rule.item))
					_rule =  check_rule_input(rules)
					print("Head extension of %s is:  %s \n" % (rules[_rule].head, rules[_rule].headExtension))

				elif(com1 == "9"):
					print("For which rule would you like to make your query? (type in name) \n")
					for k, rule in rules.items():
						print("%s: %s \n" % (k, rule.item))
					_rule =  check_rule_input(rules)
					print(rules[_rule].body)
				elif(com1 == "10"):
					print("For which rule would you like to make your query? (type in name) \n")
					for k, rule in rules.items():
						print("%s: %s \n" % (k, rule.item))
					_rule =  check_rule_input(rules)
					print(rules[_rule].head)

				elif(com1 == "11"):
					for k, v in constraints:
						print(v.name, v.item)


				elif (com1 == "12"):
					for rule in rules.values():
						print("%s: %s - %s \n" % (rule.name, rule.item, rule.weight) )

				elif (com1 == "13"):
					for w, world in worlds.items():
						print("World: %s \n" %  (world.name))
						for d in world.dependency:
							print(d.name, end=' ')

				else:
					print("I'm sorry, you did not input a recognized command, please try again. \n")
		elif(com == "13"):
			print("")

		elif(com == "14"):
			file.close()
			break
		else:
			print("I'm sorry, you did not input a recognized command, please try again. \n")
		more = ""
		while(more != "y" and more != "n"):
			more = input("Would you like to make another query?  (y, n) \n")
		if(more == 'n'):
			file.close()
			break
