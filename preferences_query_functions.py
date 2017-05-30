#Query Functions

#Since the F attribute of worlds is a set (the set of rules violated by a world) we can compare different worlds through
#set operations with respect to F
def compare_worlds(u, v, worlds):
	#a = int(u[1:])
	#b = int(v[2:])
	v = v.lstrip()
	#print("Test: %s, %s \n" % (a, b))
	if(worlds[u].F == worlds[v].F):
		print("%s and %s are equally preferable \n," % (worlds[u].name, worlds[v].name))
		return
	elif (worlds[u].F >= worlds[v].F):
		print("%s is preferable to %s \n" % (worlds[u].name, worlds[v].name))
		return
	elif worlds[b].F >= worlds[a].F:
		print("%s is preferable to %s \n" % (worlds[u].name, worlds[v].name))
		return
	else:
		print("%s and %s are not comparable in terms of preference \n" % (worlds[u].name, worlds[v].name))
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
	for world in worlds.values():
		if world.state == _state:
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
					print(worlds[world].name)
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

def worst_worlds(worlds):
	most_violated = []
	#worlds.sort(key=lambda x: len(x.F), reverse=True)
	sorted_worlds = sorted(worlds.values(), key = lambda x: len(x.F), reverse = True)
	#orted(data.items(), key=lambda x:x[1])
	#sorted_x = sorted(x.items(), key=operator.itemgetter(1))
	#most = len(worlds[0].F)
	#print("Most: %s \n")
	most = sorted_worlds[0].F
	cont = True
	for i in sorted_worlds:
		#print("World: %s, has F: %s \n" % (i.name, i.F))
		if(i.F) < most:
		#if( len(i.F) < most ):
			return most_violated
		else:
			most_violated.append(i)

def dom_of_r_in_w(_rule, _world, rules, worlds):
	result = []
	#_temp = re.findall(r'\d+', _world)
	#temp = int(_temp[0])
	for r, rule in rules.items():
		a = (r, _rule)
		if a in worlds[_world].dom:
            #print("Does this ever happen?")
			result.append(r)
	return result

def check_rule_input(rules):
	_rule = ""
	rule_names = get_rule_names(rules)
	while(_rule not in rule_names):
		_rule = input()
		if _rule not in rule_names:
			print("You did not enter a rule name, please try again\n")
	return _rule

def check_world_input(worlds):
	_world = ""
	world_names = get_world_names(worlds)
	while(_world not in world_names):
		_world = input()
		if(_world not in world_names):
			print("You did not enter a world name, please try again \n")
	return _world

def check_rule_world_pair_input(worlds, rules):
	while(True):
		pair = input()
		pair = re.sub(r"\s+", "", pair)
		while("," not in pair):
			print("There must be a comma between the rule and the world\n")
			pair = input()
			pair = re.sub(r"\s+", "", pair)
		pair = pair.split(",")
		rule_names = get_rule_names(rules)
		world_names = get_world_names(worlds)

		while(pair[0] not in rule_names or pair[1] not in world_names):
			print("pair: %s \n" % (pair))
			print("You did not enter a rule/world pair or did not enter it in the correct format (ri, wj), please try again \n")
			pair = input()
			pair = re.sub(r"\s+", "", pair)
			pair = pair.split(",")
			rule_names = get_rule_names(rules)
			world_names = get_world_names(worlds)

			if(pair[0] not in rule_names or pair[1] not in world_names):
				print("You did not enter a rule/world pair or did not enter it in the correct format (ri, wj), please try again \n")
		return pair
