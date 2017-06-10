


def assign_rule_violations_recursive(worlds, rules, dominations):
	print("Assigning rule violations ________________________________________________________________________________")
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
