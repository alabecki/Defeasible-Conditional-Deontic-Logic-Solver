import sympy.abc
from sympy.logic.boolalg import Not, And, Or, Implies
from sympy.logic import simplify_logic
from sympy import*
from sympy.logic.inference import satisfiable, valid
from sympy.logic.boolalg import to_cnf, to_dnf
from mpmath import*
import mpmath
from itertools import product
from itertools import*
import pprint
import re
from pprint import*
from copy import deepcopy
import os
from random import choice 
import sys



def base():
	do = ""
	res = []
	while len(res) == 0:
		print("\n")
		print("What would you like to do? \n")
		do = input("1: Open a file, 2: Exit program\n")
		if(do == "2"):
			sys.exit()
		if(do == "1"):
			print("Please input the name of a text-file containing a set of rules ")
			print("(or press 'r' to return) \n")
			name = input()
			if name != "r":
				res = get_file(name)
				if res == []:
					continue
				#print(type(res))
				return res


def get_file(name):
# Returns an opened file and its name
	while True:
		if name.endswith(".txt") == False:
			name = name + ".txt"
		if(os.path.exists(name)):
			_file = open(name, "r+")
			print("\n")
			print("Name of file: %s " % (name))
			res = [_file, name]
			return res
		else:
			print("The file you selected does not exist, please try again")
			print("(Or press 'r' to return) \n ")
			name = input()
			if name == 'r':
				res = []
				return res

def get_atoms(formula):
# Returns the propositional atoms form the given formula
	for ch in formula:
		ch = Symbol(ch)
	formula = Symbol(formula)
	return formula.atoms()


def obtain_atomic_formulas(file):
# Returns the propositional atoms form the given formula
	propositions = set()
	for f in file:
		f = f.lstrip()
		if f.startswith("#"):
			continue
		if len(f) >= 1:
			if f[0].isdigit():
				#f = f.lstrip()
				g = ''.join([i for i in f if not i.isdigit()])
				g = g.replace(".", "")
				g = g.replace("~", "")
				g = g.replace("&", ",")
				g = g.replace("|", ",")
				g = g.replace("(", "")
				g = g.replace(")", "")
				g = g.replace("<->", ",")
				g = g.replace("->", ",")
				g = g.replace("!", "")
				g = g.replace("TRUE", "")
				g = g.replace("FALSE", "")
				g = g.strip()
				new_props = g.split(",")
				new_props = list(filter(None, new_props))
				for prop in new_props:
					if prop == "":
						continue
					prop = prop.strip() 
					new = Symbol(prop)
					propositions.add(new)
				#propositions.add(_new)
	return propositions


def is_literal(formula):
# Checks whether a formula is a literal
	temp = str(formula)
	for ch in temp:
		if ch == "|" or ch == "&":
			return False
	return True

def all_literals(formulas):
#checks if all formulas in an array or set are literals
	for f in formulas:
		if len(f) != 1:
			return False
	#print("All remaining clauses are literals")
	return True

def contains_empty(formulas):
# Checks if any of the formulas (or clauses, rather) are empty
	for f  in formulas:
		if len(f) == 0:
			return True
	return False 

def set_to_formulas(fset):
# Converts a set of clauses into compound formula
	temp = str(fset)
	temp = temp.replace("{", "")
	temp = temp.replace("}", "")
	temp = temp.replace(",", "&")
	for ch in temp:
		ch = Symbol(ch)
	return temp


def matched(st, start):
	end_pos = start
	count = 0
	st = st[start:]
	for i in st:
		#print(i)
		#print("Count: %s " % (count))
		#print (end_pos)
		if i == "(":
			count += 1
		if i == ")":
			count -= 1
		if count == 0:
		#	print("RETURN_________________________________________-")
			return end_pos
		end_pos += 1
	return 0


def input_to_cnf(formula, propositions):
	#for f in formula:
	#	f = Symbol(f)
	#formula = Symbol(formula)
	formula = formula.strip()
	g = to_cnf(formula)
	#print("g : %s" % (g))
	temp = str(g)
	if "And" not in temp and "Or" not in temp:
		result = "(" + temp + ")"
	else:
		if temp.startswith("And"):
			temp = temp.replace("And", "")
			temp = temp[1:]
			temp = temp[:-1]
		temp = temp.split("Or")
		result = ""
		check = []
		for t in temp:
			for p in propositions:
				if "Not(" + str(p) + ")" in t:
					bef = "Not(" + str(p) + ")"
					aft = "~" + str(p)
					t = t.replace(bef, aft)
			t = t.strip()
			if t.endswith(","):
				t = t[:-1]
			t = t.replace(",", " |")
			#print("t: %s" % (t))
			if t == "" or t == " ":
				continue
			t = re.split(r'\|\s*(?![^()]*\))', t)
			for item in t:
				flag = True
				for prop in propositions:
					if "~" + str(p) in item:
						if "(" + str(p) in item or " " + str(p) in item or "|"+str(p) in item:
							flag = False
				if flag == False:
					continue
				if item not in check:
					result = result + " & " + item
					check.append(item)
		result = result.replace("&", "", 1)
	#print("Result: %s" % (result))
	return(result)


def convert_to_cnf(formulas, propositions):
# Reads file of formulas and converts them to CNF. It returns (1) a string of all the formulas put together 
# in CNF, and (2) and ordered pair of each formual and its specific CNF
	result = ""
	trans = []
	h = ""
	check = []
	for f in formulas:
		f = f.lstrip()
		if f.startswith("#"):
			continue
		if len(f) >= 1:
			if f[0].isdigit():
				#f = f.lstrip()
				g = ''.join([i for i in f if not i.isdigit()])
				g = g.replace(".", "")
				#print(g)
				g = g.lstrip()
				g = g.rstrip()
				#print("Before -> replace: %s" % (g))
				h = g.replace("->", ">>")
				#print("After -> replace: %s" % (g))
				h = input_to_cnf(h, propositions)
				h = h.strip()
				trans.append([g, h])
				#print("%-15s  %s %s" % (g, " to CNF: ", h))

		if result == "":
			result = h
		else:
			if h not in check:
				result = result + " & " + h
				check.append(h)
				#print("Result: %s" % (result))
	return [result, trans] 



def pre_cnf_to_cnf(formula, propositions):
# Takes a CNF formula in prefix notation and returns it in infix notation
	temp = to_cnf(formula)
	temp = str(temp)
	#print("temp: %s" % (temp))
	if temp.startswith("And"):
		temp = temp.replace("And", "")
		temp = temp[1:]
		temp = temp[:-1]
	#print(temp)
	temp = temp.split("Or")
	result = ""
	check = []
	for t in temp:
		#print("t %s" % (t))
		for p in propositions:
			if "Not(" + str(p) + ")" in t:
				bef = "Not(" + str(p) + ")"
				aft = "~" + str(p)
				t = t.replace(bef, aft)
				#print("t: %s " % (t))
		t = t.strip()
		if t.endswith(","):
			t = t[:-1]
		t = t.replace(",", " |")
		if t == "" or t == " ":
			continue
		t = re.split(r'\|\s*(?![^()]*\))', t)
		for item in t:
			flag = True
			for prop in propositions:
				if "~" + str(p) in item:
					if "(" + str(p) in item or " " + str(p) in item or "|"+str(p) in item:
						flag = False
			#print (flag)
			if flag == False:
				continue
			if item not in check:
				result = result + " & " + item
				#print("add item: %s" % (item))
				check.append(item)
	result = result.replace("&", "", 1)
	return(result)

def cnf_to_set(formula):
# Takes a CNF formula (infix notation) and returns the corresponding set of clauses 
	result = []
	formula = formula.replace("(", "")
	formula = formula.replace(")", "")
	#formula = formula.replace("&", "")
	formula = formula.split("&")
	for f in formula:
		addition = set()
		#print("Item: %s " % (f))
		f = str(f)
		if "|" not in f:
			f = f.strip()
			addition.add(f)
		else:
			f = f.split("|")
			for i in f:
				#print(i)
				i = i.strip()
				addition.add(i)
		if addition not in result:
			result.append(addition)
	return result




def add_query(query, propositions, fset, proof, step_tracker):
# Input query to be checked against the KB
	mfset = deepcopy(fset)
	if query != "":
		query = " ~(" + query + ")"
		query = query.lstrip()
		query = query.rstrip()
		#print(mquery)
		mquery = query.replace("->", ">>")
		#print("mquert after -> replace: %s" % (mquery))
		try: 
			mquery = to_cnf(mquery)
		except SyntaxError:
			print("The input was not a well formed function")
			query = input("Please try again")
			mfset =add_query(query, propositions, fset, proof, step_tracker)
			return mfset

		#print("query in cnf %s" % (mquery))
		mquery = pre_cnf_to_cnf(mquery, propositions)		
		mquery = cnf_to_set(mquery)
		#print("1: %s" % (mquery))
		#temp = set()
		count = len(proof.keys()) + 1
		for item in mquery:
			#print("Item --- %s" % (item))
			mfset.append(item)
			proof[str(count)] = [str(item), "Negated Conclusion"]
			item = sorted(item)
			step_tracker[str(item)] = str(count)
			count += 1
		#print("Step tracker at end of add_query")
		#for step in step_tracker:
		#	print(step)
		if len(mquery) == 1:
			print("%s is added to the KB to test for consistancy" % (mquery[0]))
		if len(mquery) > 1:
			print("The following clauses are added to the KB to test for consistancy: ")
			for pq in mquery:
				print(pq)
		#print("New mfset: %s" % (mfset))

	return mfset
	
def setup_proof_tracking(fset):
# Initiates a "proof tracking" dictionary. Used in printing out resulting proof
	proof = dict()
	step = 1
	step_tracker = dict()
	for c in fset:
		proof[str(step)] = [str(c), "Given"]
		c = sorted(c)
		step_tracker[str(c)] = str(step)
		step += 1
	return [proof, step_tracker]

def eliminate_supersets(clauses, d):
# Used to eliminate superset clauses when employing resolution 
	shadow = deepcopy(clauses)
	for i in clauses:
		for j in clauses:
			if i.issubset(j) and i != j:
				if j in shadow:
					if d == 1:
						print("%s is eliminated because it is a superset of %s " % (j, i))
					shadow.remove(j)
	return shadow

def eliminate_unipolar(clauses, props, d):
# Used to eliminate clauses containing unipolar propositions when employing resolutions 
	shadow = deepcopy(clauses)
	sprops = deepcopy(props)
	#print("sprops:")
	#for sp in sprops:
		#print(sp)
	for p in props:
		t_flag = False
		f_flag = False
		#print(len(shadow))
		for c in clauses:
			if str(p) in c:
				#print("%s true in %s " % (p, c))
				t_flag = True
			if "~" + str(p) in c:
				#print("%s false in %s " % (p, c))
				f_flag = True 
		if t_flag == True and f_flag == False:
			if d == 1:
				print("%s is always true, so all clauses containing %s will be eliminated" % (p, p))
			if p in sprops:
				print("%s is removed from the list of propositions" % (p))
				sprops.discard(p)
			for c in clauses:
				if str(p) in c and c in shadow:
					print("Eliminating %s" % (c))
					shadow.remove(c)
		if t_flag == False and f_flag == True:
			if d == 1:
				print("%s is always false, so all clauses containing ~%s will be eliminated" % (p, p))
			if p in sprops:
				print("%s is removed from the list of propositions" % (p))
				sprops.discard(p)
			for c in clauses:
				if "~" + str(p) in c and c in shadow:
					print("Eliminating %s " % (c))
					shadow.remove(c)

	return [shadow, sprops]


def eliminate_tautologies(clauses, propositions, d):
# Used to eliminate tautological clauses when employing resolution 
	shadow = deepcopy(clauses)
	for p in propositions:
		for c in clauses:
			if str(p) in c and "~" + str(p) in c:
				#print("tautology %s" % (c))
				if c in shadow:
					if d == 1:
						print("%s is removed because it is a tautology" % (c))
					shadow.remove(c)
	return shadow

def get_atom(literal):
# Used to get the atom corresponding to a given literal
	literal = str(literal)
	literal = literal.strip("~")
	return literal 


def find_empty(clauses):
# Used to find empty clauses 
	for c in clauses:
		if len(c) == 0 or "False" in c:
			return True
	return False

def literal_consistancy(clauses, propositions):
#In resolution, check if a set of literals is consistant
	for p in propositions:
		p = str(p)
		pp = set()
		pp.add(p)
		n = "~" + str(p)
		nn = set()
		nn.add(n)
		if pp in clauses and nn in clauses:
			#print("The set of literals is inconsistant")
			return False
	#print("The set of literals is consistant")
	return True 

def count_negations(a):
#Counts the number of negations attached to a formula (usually to an atom)
	a = str(a)
	count = 0
	for ch in a:
		if ch == "~":
			count += 1
	return count 

def resolve(a, clauses, props, proof, step_tracker, d):
# Used to apply the resoltuon rule on a set of clauses with respect to a literal a
	#print("Current step tracker:_____________")
	#for step in step_tracker.keys():
	#	print(step)
	#print("__________________________________")
	trash = []
	a = str(a)
	b = ""
	count = len(proof.keys()) + 1
	#print("a: %s" % (a))
	shadow = deepcopy(clauses)
	if a.startswith("~"):
		b = a[1:]
	else:
		b = "~" + a
	for i in clauses:
		#print(i)
		for j in clauses:
			#print(j)
			if a in i and b in j:
				resolvant = i.union(j)
				minus = {a, b}
				if d == 1:
					print(str(i) + " is to be resolved with " + str(j) + ": ")
					print("\n")
					print("   " + str(resolvant))
					print("______________________________")
				resolvant = resolvant.difference(minus)
				first = str(sorted(i))
				second = str(sorted(j))
				proof[str(count)] = [str(resolvant), str(step_tracker[first]) + ", " + str(step_tracker[second])]
				item = sorted(resolvant)
				step_tracker[str(item)] = str(count)
				count += 1
				
				if len(resolvant) == 0 and d == 1:
					print("    {  }    \n")
				if d == 1:
					print("   " + str(resolvant) + "\n")
				if resolvant not in clauses:
					clauses.append(resolvant)
				if i not in trash:
					trash.append(i)
				if j not in trash:
					trash.append(j)
				
				if len(resolvant) == 0:
					#print("   {  }    \n")
					if d == 1:
						print("The empty clause has been derived")
					return False
	if d == 1:			
		print("The resolved clauses are now removed:")
	for t in trash:
		if d == 1:
			print(t)
		clauses.remove(t)
	if d == 1:
		print("Remaining Clauses:")
		for c in clauses:
			print(c)
	a = get_atom(a)
	a = Symbol(a)
	#print(a)
	if a in props:
		if d == 1:
			print("%s is removed from the set of Propositions\n" % (a))
		props.remove(a)
	return True

def update_unit_clauses(clauses):
#Used to update the set of unit clauses (those clauses that consist of a literal)
	unit_clauses = []
	for c in clauses:
		if len(c) == 1:
			for i in c:
				unit_clauses.append(i)
	return unit_clauses

def resolution(clauses, propositions, proof, step_tracker):
# Main resolution function - includes diagonstic prints for the user
	step = len(proof.keys()) + 1
	print("\n")
	print("################################\n")
	print("Beginning Resolution Refutation:")
	print("################################")
	props = deepcopy(propositions)
	
	negated_conclusion = []
	for k, v in proof.items():
		#print(v[1])
		if v[1] == "Negated Conclusion":
			for p in propositions:
				if "~" + str(p) in str(v[0]):
					negated_conclusion.append("~" + str(p))
				elif str(p) in str(v[0]):
					negated_conclusion.append(str(p))

	print("Negated Conclusion Items")
	for nc in negated_conclusion:
		print(nc)
	while True:
		num_clauses = len(clauses)
		print("Clauses at start of the round:")
		for c in clauses:
			print(c)
		if find_empty(clauses):
			print("Empty clause found: %s" % ())
			return False
		if all_literals(clauses):
			print("All remaining clauses are literals")

			if literal_consistancy(clauses, propositions):
				print("The set of literals is consistant")

				return True
		clauses = eliminate_tautologies(clauses, props, 1)
		clauses = eliminate_supersets(clauses, 1)
		rest = eliminate_unipolar(clauses, props, 1)
		clauses = rest[0]
		props = rest[1]
		if len(clauses) == 0:
			return True
		if len(clauses) < num_clauses:
			print("Clauses after preliminaries:")
			for c in clauses:
				print(c)
		
		unit_clauses = update_unit_clauses(clauses)
		print("Unit Clauses:")
		for uc in unit_clauses:
			print(uc)

		print("Employment of the Resolution Rule:")
		negated_unit = []
		for nc in negated_conclusion:
			#print("nc: %s" % (nc))
			for uc in unit_clauses:
				#print("uc: %s" % (uc))
				if nc == uc:
					negated_unit.append(nc)
		if len(negated_unit) > 0:
			print("Negated Units:")
			for nu in negated_unit:
				print(nu)
			a = choice(negated_unit)
			print("%s is both a unit clause and occurs in the negated conclusion, so it is an ideal choice:" % (a))
			if str(a).startswith("~"):
				negs = count_negations(a)
				if negs % 2 == 0:
					a = str(a).strip("~")
				else:
					a = str(a).strip("~")
					a = "~" + str(a) 
			if resolve(a, clauses, props, proof, step_tracker, 1):
				negated_unit.remove(a)
				if a in negated_conclusion:
					negated_conclusion.remove(a)
				unit_clauses = update_unit_clauses(clauses)
				clauses = eliminate_tautologies(clauses, props, 1)
				clauses = eliminate_supersets(clauses, 1)
				rest = eliminate_unipolar(clauses, props, 1)
				clauses = rest[0]
				props = rest[1]
			else:
				return False
		elif len(unit_clauses) > 0:
			a = choice(unit_clauses)
			print("%s is chosen from the remaining unit clauses \n" % (a))
			if str(a).startswith("~"):
				negs = count_negations(a)
				if negs % 2 == 0:
					a = str(a).strip("~")
				else:
					a = str(a).strip("~")
					a = "~" + str(a) 
			if resolve(a, clauses, props, proof, step_tracker, 1):
				unit_clauses = update_unit_clauses(clauses)
				clauses = eliminate_tautologies(clauses, props, 1)
				clauses = eliminate_supersets(clauses, 1)
				rest = eliminate_unipolar(clauses, props, 1)
				clauses = rest[0]
				props = rest[1]

			else:
				return False

		elif len(negated_conclusion) > 0:
			a = choice(negated_conclusion)
			print("%s is chosen because it is found in the negation of the conclusion" % (a))
			if str(a).startswith("~"):
				negs = count_negations(a)
				if negs % 2 == 0:
					a = str(a).strip("~")
				else:
					a = str(a).strip("~")
					a = "~" + str(a) 
			if resolve(a, clauses, props, proof, step_tracker, 1):
				negated_conclusion.remove(a)
				unit_clauses = update_unit_clauses(clauses)
				clauses = eliminate_tautologies(clauses, props, 1)
				clauses = eliminate_supersets(clauses, 1)
				rest = eliminate_unipolar(clauses, props, 1)
				clauses = rest[0]
				props = rest[1]
			else:
				return False

		elif len(props) > 0:
			a = choice(list(props))
			print("%s is chosen" % (a))
			res = resolve(a, clauses, props, proof, step_tracker, 1)
			unit_clauses = update_unit_clauses(clauses)
			clauses = eliminate_tautologies(clauses, props, 1)
			clauses = eliminate_supersets(clauses, 1)
			rest = eliminate_unipolar(clauses, props, 1)
			clauses = rest[0]
			props = rest[1]
			if res == False:
				return False

		else:
			return True


def resolution_no_diagonsis(clauses, propositions, proof, step_tracker):
# Same as the resolution function but does not print diagnosis 
	step = len(proof.keys()) + 1
	props = deepcopy(propositions)
	
	negated_conclusion = []
	for k, v in proof.items():
		#print(v[1])
		if v[1] == "Negated Conclusion":
			for p in propositions:
				if "~" + str(p) in str(v[0]):
					negated_conclusion.append("~" + str(p))
				elif str(p) in str(v[0]):
					negated_conclusion.append(str(p))
	while True:
		num_clauses = len(clauses)
	
		if find_empty(clauses):
			return False
		if all_literals(clauses):

			if literal_consistancy(clauses, propositions):

				return True
		clauses = eliminate_tautologies(clauses, props, 0)
		clauses = eliminate_supersets(clauses, 0)
		rest = eliminate_unipolar(clauses, props, 0)
		clauses = rest[0]
		props = rest[1]
		if len(clauses) == 0:
			return True

		unit_clauses = update_unit_clauses(clauses)
		negated_unit = []
		for nc in negated_conclusion:
			#print("nc: %s" % (nc))
			for uc in unit_clauses:
				#print("uc: %s" % (uc))
				if nc == uc:
					negated_unit.append(nc)
		if len(negated_unit) > 0:
			a = choice(negated_unit)
			if str(a).startswith("~"):
				negs = count_negations(a)
				if negs % 2 == 0:
					a = str(a).strip("~")
				else:
					a = str(a).strip("~")
					a = "~" + str(a) 
			if resolve(a, clauses, props, proof, step_tracker, 0):
				negated_unit.remove(a)
				if a in negated_conclusion:
					negated_conclusion.remove(a)
				unit_clauses = update_unit_clauses(clauses)
				clauses = eliminate_tautologies(clauses, props, 0)
				clauses = eliminate_supersets(clauses, 0)
				rest = eliminate_unipolar(clauses, props, 0)
				clauses = rest[0]
				props = rest[1]
			else:
				return False
		elif len(unit_clauses) > 0:
			a = choice(unit_clauses)
			if str(a).startswith("~"):
				negs = count_negations(a)
				if negs % 2 == 0:
					a = str(a).strip("~")
				else:
					a = str(a).strip("~")
					a = "~" + str(a) 
			if resolve(a, clauses, props, proof, step_tracker, 0):
				unit_clauses = update_unit_clauses(clauses)
				clauses = eliminate_tautologies(clauses, props, 0)
				clauses = eliminate_supersets(clauses, 0)
				rest = eliminate_unipolar(clauses, props, 0)
				clauses = rest[0]
				props = rest[1]

			else:
				return False

		elif len(negated_conclusion) > 0:
			a = choice(negated_conclusion)
			if str(a).startswith("~"):
				negs = count_negations(a)
				if negs % 2 == 0:
					a = str(a).strip("~")
				else:
					a = str(a).strip("~")
					a = "~" + str(a) 
			if resolve(a, clauses, props, proof, step_tracker, 0):
				negated_conclusion.remove(a)
				unit_clauses = update_unit_clauses(clauses)
				clauses = eliminate_tautologies(clauses, props, 0)
				clauses = eliminate_supersets(clauses, 0)
				rest = eliminate_unipolar(clauses, props, 0)
				clauses = rest[0]
				props = rest[1]
			else:
				return False

		elif len(props) > 0:
			a = choice(list(props))
			res = resolve(a, clauses, props, proof, step_tracker, 0)
			unit_clauses = update_unit_clauses(clauses)
			clauses = eliminate_tautologies(clauses, props, 0)
			clauses = eliminate_supersets(clauses, 0)
			rest = eliminate_unipolar(clauses, props, 0)
			clauses = rest[0]
			props = rest[1]
			if res == False:
				return False

		else:
			return True
	

















































