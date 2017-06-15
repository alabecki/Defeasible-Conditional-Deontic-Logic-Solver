#Query Functions

from copy import deepcopy
from preference_classes import*
from preferences_core_functions import*

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
	for k in rules.keys():
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
