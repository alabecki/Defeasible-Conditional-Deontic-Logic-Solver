#Query Functions

from preference_classes import*
from preferences_core_functions import*

from sympy import Symbol
from sympy.abc import*
from sympy.logic.boolalg import to_cnf
from sympy.logic.boolalg import Not, And, Or
from sympy.logic.inference import satisfiable, valid
from mpmath import*
import sys
from copy import deepcopy
from shutil import copyfile
from itertools import*
from itertools import product, combinations

from preferences_core_functions import*

import re

#Since the F attribute of worlds is a set (the set of rules violated by a world) we can compare different worlds through
#set operations with respect to F
def compare_worlds_by_subset(u, v, worlds):
	v = v.lstrip()
	if (worlds[u].F >= worlds[v].F):
		print("%s is preferable to %s " % (worlds[u].name, worlds[v].name))
		print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ \n")
		return
	elif worlds[v].F > worlds[u].F:
		print("%s is preferable to %s " % (worlds[u].name, worlds[v].name))
		print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ \n")
		return
	else:
		print("%s and %s are not comparable in terms of preference " % (worlds[u].name, worlds[v].name))
		print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ \n")
		return

def compare_worlds_by_cardinality(u, v, worlds):
	v = v.lstrip()
	if (len(worlds[u].F) >= len(worlds[v].F)):
		print("%s is preferable to %s " % (worlds[u].name, worlds[v].name))
		print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ \n")
		return
	elif len(worlds[v].F) >= len(worlds[u].F):
		print("%s is preferable to %s " % (worlds[u].name, worlds[v].name))
		print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ \n")
		return

def compare_worlds_by_weighted_cardinality(u, v, worlds):
	v = v.lstrip()
	if(worlds[u].weightedF <= worlds[v].weightedF):
		print(" %s is preferable to %s \n " % (worlds[u].name, worlds[v].name))
		print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ \n")
		return
	elif (worlds[v].weightedF <= worlds[u].weightedF):
		print("%s is preferable to %s \n" % (worlds[u].name, worlds[v].name))
		print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ \n")
		return

def get_rule_names(rules):
	result = []
	for k in sorted(rules.keys()):
		result.append(k)
	return result

def get_world_names(worlds):
	result = []
	for w in worlds.values():
		result.append(w.name)
	return result

#Query function to fetch the worlds in which a rule is "true"
def find_rule_extension(rule_name, rules, worlds):
	result = []
	temp = rules[rule_name]
	for w in temp.bodyExtension:
		if w in temp.headExtension:
			result.append(w)
	return result

#Query function to fetch the worlds in which a rule is "false"
def find_rule_false(rule_name, rules, worlds):
	result = []
	temp = rules[rule_name]
	for w in temp.bodyExtension:
		if(w not in temp.headExtension):
			if w not in result:
				result.append(w)
	return result

#This is used in the rare case where we have a world state (from the extension of a Rule, and need to find the world
#object corresponding to that state
def get_world_from_state(_state, worlds):
	result = ''
#	print("State " + str(_state))
	for world in worlds.values():
		#print("World " + str(world.state))
		if world.state == _state:
	#		print("check")
			result = world.name
			return result

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
	if len(f1_min) == 0:
		return
	#print("f1_min: %s" % (f1_min))
	#print("f2ext: %s" % (f2ext))
	for w in f1_min:
	#	print("w.state: %s " % (w.state))
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
				if worlds[w2j].F.issubset(worlds[w2i].F) and worlds[w2j].F != worlds[w2i].F:
					return False
			if world2j.F.issubset(world2i.F) and world2i.F != world2j.F:
				if worlds[w2i].F.issubset(worlds[w2j].F) and worlds[w2j].F != worlds[w2i].F:
					return False
			if worlds[w2i].F.issubset(worlds[w2j].F) and w2i != w2j:
				if world2j.F.issubset(world2i.F) and world2j.F != world2i.F:
					return False
			if worlds[w2j].F.issubset(worlds[w2i].F):
				if world2i.F.issubset(world2j.F)  and world2j.F != world2i.F:
					return False
			if world2i.F.issubset(world2j.F) == False:
				if worlds[w2i].F.issubset(worlds[w2j].F):
					flag = False
					return flag
			if world2j.F.issubset(world2i.F) == False:
				if worlds[w2j].F.issubset(worlds[w2i].F):
					flag = False
					return flag
			if worlds[w2j].F.issubset(worlds[w2i].F) == False:
				if world2j.F.issubset(world2i.F):
					flag = False
					return flag
			if worlds[w2i].F.issubset(worlds[w2j].F) == False:
				if world2i.F.issubset(world2j.F):
					flag = False
					return flag
	return True

def from_prefix(rule):
	res = rule.replace("Not(", "~")
	res = res.replace(")->", "->")
	res = res.replace("))", ")")
	return res

def strip_not(form):
	res = form.replace( "Not(" , "")
	res = res.replace( ")" , "")
	return res

def from_prefix2(p):
	res = p.replace("Not(", "~")
	res = res.replace(")", "")
	return res


# The remaining functions are used for various queries that the user might make.
def find_rule_violations(rule_name, rules, worlds):
	result = []
	false = find_rule_false(rule_name, rules, worlds)
	for w in false:
		#world = worlds[w]
		world = get_world_from_state(w, worlds)
		#temp = int(world[1:])
		for r, rule in rules.items():
			a = (r, rule_name)
			if( (a not in worlds[world].dom) or (worlds[world].state not in rule.bodyExtension) ):
				if worlds[world] not in result:
					#print(worlds[world].name)
					result.append(worlds[world])
	return result

def print_violations(world_name, worlds):
	result = []
	for d in worlds[world_name].F:
		result.append(d)
	return result

def print_false_rules_at_w(_world, rules, worlds):
	result = []
	for k, rule in rules.items():
		if(worlds[_world].state in rule.bodyExtension and worlds[_world].state not in rule.headExtension):
			result.append(rule.name)
	return result

def print_rules_true_at_w(_world, rules, worlds):
	result = []
	for k, rule in rules.items():
		if(worlds[_world].state in rule.bodyExtension and worlds[_world].state in rule.headExtension):
			result.append(rule.name)
	return result

def print_rules_neutral_at_w(_world, rules, worlds):
	result = []
	for k, rule in rules.items():
		if(worlds[_world].state not in rule.bodyExtension):
			result.append(rule.name)
	return result

def worst_worlds_by_subset(worlds):
	most_violated = deepcopy(worlds)
	for w1, world1 in worlds.items():
		for w2, world2 in worlds.items():
			if world2.F > world1.F:
				del most_violated[w1]
				break
	return most_violated

def worst_worlds_by_cardinality(worlds):
	most_violated = { }
	sorted_worlds = sorted(worlds.values(), key = lambda x: len(x.F), reverse = True)
	most = len(sorted_worlds[0].F)
	cont = True
	for i in sorted_worlds:
		if( len(i.F) < most ):
			return most_violated
		else:
			most_violated[i.name] = i

def worst_worlds_by_weighted_cardinality(worlds):
	most_violated = { }
	sorted_worlds = sorted(worlds.values(), key = lambda x: x.weightedF, reverse = True)
	most = sorted_worlds[0].weightedF
	cont = True
	for w in sorted_worlds:
		if w.weightedF < most:
			return most_violated
		else:
			most_violated[w.name] = w


def check_rule_input(rules):
	_rule = ""
	rule_names = get_rule_names(rules)
	while(_rule not in rule_names):
		_rule = input()
		if _rule not in rule_names:
			print("You did not enter a rule name, please try again")
			print("----------------------------------------------- \n")
	return _rule

def check_world_input(worlds):
	_world = ""
	world_names = get_world_names(worlds)
	while(_world not in world_names):
		_world = input()
		if(_world not in world_names):
			print("You did not enter a world name, please try again \n")
	return _world

def check_world_input2(world, worlds):
	world_names = get_world_names(worlds)
	wrd = world.strip(" ")
	print (wrd)
	if wrd not in world_names:
		return False 
	else:
		return True


def print_worlds_by_cardinality(worlds):
	ordered_worlds = {}
	sorted_worlds = sorted(worlds.values(), key =lambda x: len(x.F))
	print("<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><> \n")
	for i in sorted_worlds:
		print("%s: %s, %s, %s \n" % (i.name, i.state, i.F, i.weightedF))
	print("<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><> \n")


def print_worlds_by_weighed_cardinality(worlds):
	ordered_worlds = {}
	print("<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><> \n")
	sorted_worlds = sorted(worlds.values(), key =lambda x: x.weightedF)
	for i in sorted_worlds:
		print("%s: %s, %s, %s \n" % (i.name, i.state, i.F, i.weightedF))
	print("<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><> \n")

def free_generate_prop_product(propositions, rules, constraints):
	props = deepcopy(propositions)
	for p in propositions:
		neg = str(p)
		neg = "Not(" + neg + ")"
		neg = symbols(neg)
		props.add(neg)
	pairs = []
	for p in props:
		pairs.append(p)
	domain = list(product(pairs, repeat = 2))
	return domain

def restricted_generate_prop_product(propositions, rules, constraints):
	conditions = set()
	obligations = set()
	for p in propositions:
		neg = str(p)
		neg = "Not(" + neg + ")"
		neg = symbols(neg)
		for rule in rules.values():
			if str(p) in rule.body or "~" + str(p) in rule.body:
				conditions.add(p)
				conditions.add(neg)
			if str(p) in rule.head or "~" + str(p) in rule.head:
				obligations.add(p)
				obligations.add(neg)
		#for k, v in constraints.items():
		#	if str(p) in v.item or "~" + str(p) in v.item:
		#		conditions.add(p)
		#		conditions.add(neg)
		#		obligations.add(p)
		#		obligations.add(neg)
	domain = product(conditions, obligations)
	
	return domain

def set_up_implications(d, worlds, propositions):
	temp = list(d)
	if strip_not(str(temp[0])) == strip_not(str(temp[1])):
		return "nil"
	a = from_prefix2(str(temp[0]))
	b = from_prefix2(str(temp[1]))
	for c in a:
		c = symbols(c)
	for c in b:
		c = symbols(c)
	t1ext = assign_extensions(a, worlds, propositions)
	t1ext = list(t1ext)
	#print("t1ext:  %s" % (t1ext))
	t1min = get_min_F_subset(t1ext, worlds)
	if len(t1min) == 0:
		return "nil"
	#print("t1min: %s" % (t1min))
	t2ext = assign_extensions(b, worlds, propositions)
	t2ext = list(t2ext)
	res = [t1min, t2ext, a, b]
	return res
