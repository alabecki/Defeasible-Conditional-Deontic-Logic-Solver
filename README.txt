Naive Preferences Solver
_________________________________________________________________________
_________________________________________________________________________

1. Introduction:
The program reads sets of rules from text files describing defeasible, 
conditional preferences and then calculates which worlds (i.e. truth 
assignments) are most preferable. Once the best worlds are determined, 
the user may search for rules that may be implied by those which are 
given.
World preference is determined in terms of rule violation. A world w1 is 
preferable to w2 if and only if the set of rules violated in w1 is a 
subset of the rules violated in w2.
Rules must be included in the following format: (b, h), where a and b are 
formulas of propositional logic. "&" is used for "and", "|" is used for 
"or", and "~" is used for negation.
		Example:	( (~P | (~Q | R)), (Q & P) )
Constraints are formulas preceded by  an “!”
		Example:	!(~C | ~F)
The program makes use of the SAT solver included in sympy, which requires 
mpath. It also utilizes the Symbol object, with which formulas are 
encoded for the purpose of using the SAT solver.

2. Rules:
The conditional nature of the rules is made evident in their form.  A 
rule is an ordered pair of propositional formulas (b, h), where the first 
item is the "body" and the second item is the "head". If the body is true 
then, all other things being equal, the head should be so as well. The 
body is the condition, the obtaining of which renders the head obligatory 
unless the rule is defeated by another rule.
Rule r is true at world w just in case both its body and head are true at 
w.
Rule r is neutral at world just in case its body is false at w (the 
condition does not obtain).
Rule r is said to be false at world w just in case the body of r is true 
in w but the head is false at w.
If rule r is false at w and r is not defeated at w, then it is violated 
at w. Defeasibility is explained in the next section.
To express an unconditional preference, simply leave the body blank ( , 
h). h will be preferred no matter what else might be the case. 

3. Domination:
To make rules defeasible, it is necessary to provide conditions under 
which they may be overwritten or defeated by other rules. In general, 
rules with more specific bodies will dominate those with less specific 
bodies. Specificity, in turn, is understood in terms of material 
implication. Formula p is more specific than formula q just in case p 
implies q but q does not imply p. Rules, then, will typically be made 
more specific by adding conjuncts the body and are made less specific by 
adding disjuncts to the body. The formulas below become increasingly more 
specific from 1 to 5:
	(1)	(p | q) |r
	(2)	(p | q)
	(3)	p
	(4)	p & q
	(5)	(p & q) & r
There is also a second condition for domination. To dominate r, r’ must 
be more specific and it must the be case that the heads of r and r’ 
cannot both be true. If the head of r’ does not essentially contradict 
the head of r, then it can hardly override r. 
If r is false at w and r’ dominates r, then r’ will override r just in 
case its body is true at w. In this case, r is said to be defeated by r’.
It should be noted that if r’ is, in turn, defeated by r”, then r will no 
longer be defeated by r’ (unless, of course r” is defeated). The program 
searches for these cases recursively. 

4. Constraints
Constraints can also be included to require that a given formula holds. 
The effect is that worlds that do not satisfy the constraint are excluded 
from consideration.
Constraints can be used to enforce rules in which an exclusive 
disjunction is understood to hold, which is very often the case, because 
when we say we prefer A to B and B to C, it is often the case that only 
one will be selected.
(When all choices are binary, such a constraint need not be made if the 
alternatives are expressed in propositions and their negation)

5. Best Worlds
The best worlds are determined in terms of rule violations. For a world 
w, let w.F be the set of rules violated at w. A world w is among the best 
worlds just in case there does not exist a world w’ such that w’.F is a 
subset of w.F. 

6. Inferred Rules
The set of best worlds is used to consider any rules that may be implied 
by those that are explicitly given in the text file. If W+ is the set of 
best words given rule set R, then rule r is implied by R just in case W+ 
remains the set of best world the union of R and r.   
_________________________________________________________________________
_________________________________________________________________________

WARNING: The solver does not seem to like "N" or "S" for some reason, so 
do not use these in your rules or the program will likely crash.
All lowercase letters appear to work fine as propositions.

REMARK: Expressing preferences in propositional logic can be a bit 
tricky. For instance, suppose we want to encode the following preference: 
C > T > F.
This can be expressed in the form of three rules:
( ,  C)
( ~C, T)
(~(T | C), F)
