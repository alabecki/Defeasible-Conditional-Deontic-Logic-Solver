
#/usr/bin/python3
#Propositional Logic Assistant - Main File


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


import sympy.abc
from sympy.logic.boolalg import Not, And, Or
from sympy import*
from sympy.logic.inference import satisfiable, valid
from sympy.logic.boolalg import to_cnf
from mpmath import*
import mpmath
from itertools import product
from itertools import*
import pprint
import re
from sys import*
from copy import deepcopy

from os import*

from PLA_functions import*


commands = {
	"1": "Convert the KB to Conjunctive Normal Form (CNF)",
	"2": "Make Resolution Refutation Query with Respect to the KB",
	"3": "Get set of Models that satisfy the KB",
	"4": "Get the set of Models that satisfy a query given the KB",
	"5": "Return"
}

resol = {
	"1": "Just tell me if the query is a consequence of the KB ",
	"2": "Show the Resolution Proof",
	"3": "Show the whole Diagnostic",
	"4": "Show both the Resolution Proof and the Diagnostic",
}



while True:

	res = base()

	file = res[0]
	file_name = res[1]

	file.seek(0)
	print("\n")
	print("Formulas in KB:")
	print("_________________________________________________________________________________\n")
	for f in file:
		if f[0].isdigit():
			print (f)

	file.seek(0)
	propositions = obtain_atomic_formulas(file)
	
	file.seek(0)

	#print("Conjunction: %s " % (conjunction))

	#form = pre_cnf_to_cnf(conjunction, propositions)
	#print("Form: %s " % (form))
	res2 = convert_to_cnf(file, propositions)

	form = res2[0]
	trans = res2[1]

	#print("Form %s " % (form))

	fset = cnf_to_set(form)
	#print("fset = %s" % (fset))

	file.close()

	#fset = get_sat_input(conjunction, propositions)
	#print("fset: %s " % (fset))
	while True:
		com = ""
		while com not in commands.keys():
			print("\n")
			print("What would you like to do?")
			for c, cmd in sorted(commands.items()):
				print(c, cmd)
			com = input()

		if com == "1":
			print("The given set of formulas in CNF:\n")
			for i in trans:
				print("%-25s   to CNF:   %s" % (i[0], i[1]))
			print("Combined:")
			print(form)
			print("\n")

		if com == "2":
			set_up = setup_proof_tracking(fset)
			proof = set_up[0]
			step_tracker = set_up[1]
			print("Please input a query \n")
			while True:
				query = input()
				try:
					mfset = add_query(query, propositions, fset, proof, step_tracker)
					break
				except TypeError: 
					print("\n")
					print("The input contained characters that are neither alphabetic nor booleans operators.")
					print("Please try again...")
				except SyntaxError:
					print("\n")
					print("The input was not a well-formed formula.")
					print("Please try again...")


			opt = ""
			while opt not in resol.keys():
				print("\n")
				print("Please choose one of the following options:")
				for k, v in sorted(resol.items()):
					print(k, v)
				opt = input()

			if opt == "1":
				if resolution_no_diagonsis(mfset, propositions, proof, step_tracker):
					print("\n")
					print(" %s is not entailed by the KB" % (query))
					print("___________________________________________________ \n")
				else:
					print("\n")
					print(" %s is entailed by the KB" % (query))
					print("___________________________________________________ \n")


			if opt == "2":
				if resolution_no_diagonsis(mfset, propositions, proof, step_tracker):
					print("\n")
					print(" %s is not entailed by the KB \n" % (query))
				else:
					print("\n")
					print(" %s is entailed by the KB" % (query))
					print("___________________________________________________ \n")
					print("Proof:")
					for k, v in sorted(proof.items()):
						if v[0] == "set()":
							print("%-2s: %-30s %s" % (k, "{''}", v[1]) )
						else:
							print("%-2s: %-30s %s" % (k, v[0], v[1]))

			if opt == "3":
				if resolution(mfset, propositions, proof, step_tracker):
					print("\n")
					print(" %s is not entailed by the KB" % (query))
					print("___________________________________________________ \n")
					print("(Scroll up to view diagnosis)")

				else:
					print("\n")
					print(" %s is entailed by the KB \n" % (query))
					print("___________________________________________________ \n")

					print("(Scroll up to view diagnosis)")

			if opt == "4":			
				if resolution(mfset, propositions, proof, step_tracker):
					print("\n")
					print(" %s is not entailed by the KB \n" % (query))
					print("___________________________________________________ \n")
					print("(Scroll up to view diagnosis)")
				else:
					print("\n")
					print(" %s is entailed by the KB \n" % (query))
					print("Proof:")
					for k, v in sorted(proof.items()):
						if v[0] == "set()":
							print("%-2s: %-30s %s" % (k, "{''}", v[1]) )
						else:
							print("%-2s: %-30s %s" % (k, v[0], v[1]))

					print("(Scroll up to view diagnosis)")

			if opt == "5":
				print("... ")

		if com == "3":
			
			models = satisfiable(form, all_models = True)
			models = list(models)
			if models[0] == False:
				print("The KB is not satisfied by any model\n")
			else:
				print("The KB is satisfied by the following models: \n")
				for m in models:
					print(m)

		if com == "4":
			print("Please input a query...")
			query = input()
			query = query.replace("->", ">>")
			augment = form + "& (" + query + ")"
			#print("Augment: %s" % (augment))
			models = satisfiable(augment, all_models = True)
			models = list(models)
			if models[0] == False:
				print("The KB augmented by %s is not satisfied by any model\n" % (query))
			else:
				print("The KB is satisfied by the following models: \n")
				for m in models:
					print(m)


		if com == "5":
			break





