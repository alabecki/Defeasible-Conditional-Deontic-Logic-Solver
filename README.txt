Naive Preferences Solver 
_________________________________________________________________________ 
_________________________________________________________________________ 
 
1. Introduction: 
The program is intended to model expressions and inferences in defeasibly 
conditional deontic logic. 
It reads sets of rules (R) from text files 
describing defeasible, conditional obligations and then calculates which 
worlds (i.e. truth assignments) are most preferable. Also, for any 
formula f, the best f-worlds may be calculated, which worlds are used as 
a basis for determining which inferences may be true and whether 
additional rules might be implied from those that are given. 
 
World preference is determined in terms of rule violation. For each 
world w let w.F be the set of rules violated in w. The program supports 
three options when determining preference relations between worlds. 
 
Rules in the ‘txt.’ files must be written in the following format: 
(b -> h), where 'a' and 'b' are formulas of propositional logic. "&" is 
used for "and", "|" is used for "or", and "~" is used for negation. 
		Example:	( (~p | (~q | r)) -> (q & p) ) 
Constraints are formulas preceded by  an ! 
		Example:	!(~c | ~f) 
 
The program is fairly flexible with the use of 
parentheses, provided that the outermost parentheses are present and that 
parentheses are not required to understand the meaning of the expression. 
Moreover, spacing within a rule 
is ignored. The following rule is perfectly acceptable: 
		Example (a   & ~b &c -> p | q |r) 
 
IMPORTANT: Rules and constraints must appear on lines by themselves or 
the program will be able to parse them correctly.

Rules may be given weights denoting their relative importance, where a 
higher number denotes greater importance or priority. A weight may be 
added to a rule as a float preceded by a '$' sign. 
		Example (a | c  -> ~b)  $2.3 
 
Several example txt. files are included with the program. 
 
The program makes use of the sympy SAT solver, which requires 
mpath. It utilizes the sympy Symbol object, with which formulas are 
encoded for use with the SAT solver. 
 
2. Commands: 
 
Once a txt. file has been loaded and processed by the program the 
following 
queries can be made: 
 
	1:	Show the set of most preferable worlds
	2:	Show the set of least preferable worlds
	3:	Compare two specific worlds with respect to preference
	4:	Show which rules are violated at each world ordered by number 
		of rule violations
	5:	Show which rules are violated at each world ordered by 	
		weighted number of rule violations
	6:	Show the best worlds at which a formula f is true
	7:	Determine whether, given R, the truth of 'a' makes 'b' 	
		obligatory (user provides a and b)
	8: 	Determine whether, given R, the truth 'a' makes 'b' 	
		permissible (user provides a and b)
	9:	Determine whether, given our preferences, a further rule is 
		implied (user provides new rule (a, b))
	10:	Add rule to R
	11:	Augment current rules with rules from an additional file
	12:	Additional Queries
	13:	Write data to text-file
	14:	I am done with this file  
 
Most of these commands are self-explantory. Note, again, that the user 
may choose from methdos of comparing worlds.
how worlds are com. (7) allows the user to check whether the inference 
R: a |- b is true, for any two formulas a and b. Where |- is interpreted 
in terms of obligation. (8) does the same but with permissability. (9) checks if a new rule (a -> 
b), provided by the user, is implied by those that are already given. Note that (7) will be stronger than (9), in that 
often R: a |- b will be satsified while (a -> b) will fail. (10) allows the user to add an 
additional rule r to R while (11) allows the user to add all rules (and constraints) from a file to those 
that are already in R. (12) presents user with various minor queries, most of which were made for the purpose of bug-testing, but  
have been included in case the user may find some utility in them. 
	 
_________________________________________________________________________ 
_________________________________________________________________________ 
 
WARNING: The solver does not seem to like "N" or "S" for some reason, so 
do not use these in your rules or the program will likely crash. 
All lowercase letters appear to work fine as propositions. So it is 
suggested that the user sticks to lower case letters. 
 
REMARK: Expressing preferences in propositional logic can be a bit 
tricky. For instance, suppose we want to encode the following preference: 
C > T > F. 
This can be expressed in the form of three rules: 
( ,  C) 
( ~C, T) 
(~(T | C), F) 

