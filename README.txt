 
_________________________________________________________________________
Naive Preferences Solver 
_________________________________________________________________________ 
 
0. Installation

To run the program, a computer must have Python 3.x installed. The program 
was written on Python 3.6 but may run correctly on older versions. Version 
3.4 or higher, however, is recommended. The program can be opened in on the 
command-line in Windows or Linux machines. 

In the command line, go to the directory in which you have placed the 
folder containing the program and type:

	python main.py

(If you have Anaconda installed on your computer you need only type 
“z_main.py”)

The program makes use of the logic module from the sympy library. It is 
recommended that the user employ pip when installing Python libraries. To 
install sympy simply type:

       pip install sympy	(perhaps with a “sudo”)


If you have both Python 2.x and 3.x installed on your system, it might 
run Python 2.x by default, which will cause trouble both when trying to 
run the program and when installing modules. 

If this is the case, type the following into the command prompt: 
	
	alias python='/usr/bin/python3'

Then install sympy as follows:
	
	python3.x -m pip install sympy
_________________________________________________________________________


1. Introduction: 
The program is intended to model expressions and inferences in defeasible 
conditional deontic logic, based on semantics provided by James Delgrande 
of SFU. It reads sets of rules (R) from text files describing defeasible 
and conditional obligations and then calculates which worlds (i.e. truth 
assignments or interpretations) are most preferable. For any formula f, 
the best f-worlds may be calculated, which worlds are used as a basis 
for determining which entailments obtain and whether additional rules 
might be implied from those that are given. 
 
The program supports three options when determining preference relations 
between worlds. 
_________________________________________________________________________
 
2. Rules and Constraints:
Rules in the ‘.txt’ files must be written in the following format: 
(b -> h), where 'b' and 'h' are formulas of propositional logic. "&" is 
used for "and", "|" is used for "or", and "~" is used for negation. 
Atomic propositions are be composed of one or more Latin letters. 
The sympy module reserves I, E, S, N, C, O, and Q for imaginary numbers, 
so they should not be used in propositions. For this reason it is 
recommended that the user stick with lower-case letters.   

	Example 1:	( (~par | (~qu | r)) -> (qu & par) ) 

Constraints are formulas preceded by an “!” 

	Example 2:	! ~c | ~f  
 
The program is flexible with the use of parentheses, with the 
following exceptions:

	(1) The outermost parentheses for rules must be included
	(2) Any parentheses required for understanding the meaning of the
	    expression must be included 

Spacing within a line is ignored. The following rule is 
perfectly acceptable: 

	Example 3: (a   & ~b &c -> p | q |r) 
 
IMPORTANT: Rules and constraints must appear on lines by themselves or 
the program will not be able to parse them correctly. Also, the first 
character of a rule line MUST be “(“, and the first character of a 
constraint line MUST be “!”.

Rules may be given weights denoting their relative importance, where a 
higher number denotes greater importance or priority. A weight may be 
added to a rule as a float preceded by a '$' sign.
 
		Example (a | c -> ~b)  $2.3
Rules do not need to have bodies, but they do need to have heads.
	
	Example 4: (  -> p|q)

In this example, p or q ought to be the case by default, but this 
default might be overturned by a rule with a body:
	
	Example 5: (r -> ~(p|q))

“TRUE” and “FALSE” can be used when defining rules: 
	
       Example 6: (pm & hs -> FALSE)
       
       Example 7: (TRUE -> p|q)
       
       Example 8: (~(p|q) -> FALSE)

Ex. 6 is the rule that, normally, pm and hs are not both true. Ex. 7 
and 8 are both notational variants of Ex. 4.  
	 
 
Some example ruleset text files are included with the program. 
  
________________________________________________________________________

3. Commands Overview: 
 
Once a “.txt” file has been loaded and processed by the program the 
following Primary Commands can be made: 
 
	1: Modal analysis
	2: Inferences from R
	3: Augmenting R
	4: Write Data to text-file
	5: Additional queries
	6: I am done with this file
 
Most of these commands are self-explanatory. 1 takes the user to several 
options analyzing R in largely modal terms. 2 takes the user to several 
options for testing or generating inferences from R. 3 takes the user to 
a couple of options for augmenting R with additional rules or 
constraints. 5 takes the user to various minor queries (which were 
largely created for de-bugging purposes), and 6 closes the current file 
and ruleset.
_________________________________________________________________________

4. Modal Analysis:

Modal analysis takes the user to the following options:

	1: Show the set of most preferable worlds
	2: Show the set of least preferable worlds
	3: Compare two specific worlds with respect to preference
	4: Show which rules are violated at each world ordered by number of 
	rule violations
	5: Show which rules are violated at each world ordered by weighted 
	number of rule violations
	6: Show the best worlds at which a formula f is true
 
Preferability among worlds is determined by rule-violations. There are 
three ways of evaluating preferability: If w0 is preferable to w1 then:

a. The rules violated in w0 are a subset of the worlds violated in w2, or  

b. The number of rules violated in w0 is no greater than the number of 
rules violated in w1, or 

c. The weighted rule violations in w0 are no greater than the weighted 
rule violations in w1

_________________________________________________________________________

5: Inferences from R
The user is presented with the following options:
1: For some a, b, check if R, a |= b holds with respect to obligation
2: For some a, b, check if R, a |= b holds with respect to permissibility
3: For some a, b check if R |= (a -> b) obtains 
4: Generate each instance of R |= (a -> b) for {a, b | a and b are 
literals obtained from the atoms of R}
5: Generate all entailments of obligation on R (restricted to literals)
6: Generate all entailments of permissibility on R (restricted to 
literals)

For 1, 2, and 3, ‘a’ and ‘b’ can be any arbitrary formulas of propositional
logic. 4, 5, and 6 are limited to literals because generating all formulas
is impossible and generating such instances for length 2 formulas, is 
already very slow.

6: The rest

Augmenting can be done in two ways. The first is simply to type in a new rule,
the second loads a new rule file and combines it with 
the current ruleset to generate a new one. 
 
The Additional Queries were introduced for debugging purposes but the 
user may occasionally find a few of them useful. 
 
_________________________________________________________________________ 
_________________________________________________________________________ 
 

