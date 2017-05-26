	
Naive Preferences Solver
__________________________________________________________________________________________________________________________________________________

The program reads txt. files consisting of a set of rules (and possibly constraints) describing a set of conditional preferences and then calculates which worlds
(i.e. truth assignments) are most preferable relative to the rules. A world w1 is preferable to w2 if and only if the set of rules violated in w1 is a subset of
the rules violated in w2.

The rules and constraints are expressed in terms of propositional logic.

A rule is an ordered pair of propositional fomulas (b, h), where the first item is the "body" and the second item is the "head". 
The rule expresses a preference as follows: if the body is true then, all other things being equal, the head should be so as well.

To express an unconditional preference, simply leave the body blank ( , h). h will be preferred no matter what else might be the case.

Constraints can also be included to require that a given formula holds. The effect is that worlds that do not satisify the constraint are 
excluded from consideration.
	
Rules must be included in the following fromat: (b, h), where a and b are formulas of propositional logic. "&" is used for "and", "|" is used for "or",
and "~" is used for negation.
		Example: ( (~P | (~Q | R)), (Q & P) )

Constraints are formulats preceded at a !
		Example: !(C & F)

Constraints are needed to enforce rules in which an exclusive disjunction is understood to hold, which is very often the case, becasue when we say we prefer 
A to B and B to C, it is often the case that only one will be selected. 
(When all choices are binary, such a constraint need not be made if the alternatives are expressed in propositions and their negation)

The program makes use of the SAT solver included in sympy, which requires mpath. It also utilizes the Symbol object, with which formulas are encoded
for the purpose of using the SAT solver.
______________________________________________________________________________________________________________________________________________________

WARNING: The solver does not seem to like "N" or "S" for some reason, so do not use these in your rules or the program will likely crash.
All lower case letters appear to work fine as propositions.


REMARK: Expressing preferences in propositional logic can be a bit tricky. For instance, suppose we want to encode the following preference: C > T > F.
This can be expressed in the form of three rules: 
 
( ,  C)
( ~C, T)
(~(T | C), F)



 