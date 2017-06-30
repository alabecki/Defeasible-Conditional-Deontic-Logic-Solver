Naive Preferences Solver 
_________________________________________________________________________ 
_________________________________________________________________________ 
 
0. Installation
To run the program, a computer must have Python 3.x installed.
The program was written on Python 3.6 but may run correctly on older 
versions. It is recommended that the user should be using 3.4 or higher.
The program can be opened in on the command-line in Windows or Linux
machine. 

In the command line, go to the directory in which you have placed the 
folder containing the program and type:

	python main.py

(If you have Anaconda installed on your computer you need only type 
“main.py”)

The program makes use of the logic module from the sympy library, which 
is itself dependent upon the pmath library. If these have not been 
installed, the user will be informed when trying to run the program. 
It is recommended that the user use pip when installing Python libraries.
To install sympy and pmath using pip simply type:

pip install sympy
pip install pmath

(Linux users may need to preface these commands with the customary 
“sudo”)

_________________________________________________________________________


1. Introduction: 
The program is intended to model expressions and inferences in defeasible 
conditional deontic logic. It reads sets of rules (R) from text files 
describing defeasible and conditional obligations and then calculates 
which worlds (i.e. truth assignments or interpretations) are most 
preferable. Also, for any formula f, the best f-worlds may be calculated, 
which worlds are used as a basis for determining which entailments obtain 
and whether additional rules might be implied from those that are given. 
 
The program supports three options when determining preference relations 
between worlds. 
_________________________________________________________________________
 
2. Rules and Constraints:
Rules in the ‘.txt’ files must be written in the following format: 
(b -> h), where 'a' and 'b' are formulas of propositional logic. "&" is 
used for "and", "|" is used for "or", and "~" is used for negation. 
Atomic propositions must be Latin letters. Some upper-case letters, 
notably “N” and “S” often cause the SAT solver to crash, so it is 
recommended that the user stick with lower-case letters.  

		Example:	( (~p | (~q | r)) -> (q & p) ) 

Constraints are formulas preceded by an “!” 

		Example:	! ~c | ~f  
 
The program is fairly flexible with the use of parentheses, with the 
following exceptions:
	(1) The outermost parentheses for rules must be included
	(2) Any parentheses required for understanding the meaning of the
	expression must be included 

Moreover, spacing within a line ignored is ignored. The following rule is 
perfectly acceptable: 

		Example: (a   & ~b &c -> p | q |r) 
 
IMPORTANT: Rules and constraints must appear on lines by themselves or 
the program will not be able to parse them correctly. Also, the first 
character of a rule line MUST be a “(“, and the first character of a 
constraint line MUST be a “!”.

Rules may be given weights denoting their relative importance, where a 
higher number denotes greater importance or priority. A weight may be 
added to a rule as a float preceded by a '$' sign.
 
		Example (a | c -> ~b)  $2.3 
 
Several example txt. files are included with the program. 
  
_________________________________________________________________________

3. Commands: 
 
Once a .txt file has been loaded and processed by the program the 
following Primary Commands can be made: 
 
	1: Modal analysis
	2: Inferences from R
	3: Augmenting R
	4: Write Data to text-file
	5: Additional queries
	6: I am done with this file
 
Most of these commands are self-explanatory. 1 takes the user to several 
options analyzing R in largely modal terms. 2 takes the user to several 
options for testing or generating inferences from R, 3 takes the user to 
a couple of options for augmenting R with additional rules or 
constraints. 5 takes the user to various minor queries (which were 
largely created for de-bugging purposes), and 6 closes the current file 
and ruleset.

More specifically, Modal analysis takes the user to the following 
options:
	1: Show the set of most preferable worlds
	2: Show the set of least preferable worlds
	3: Compare two specific worlds with respect to preference
4: Show which rules are violated at each world ordered by number of rule 
violations
5: Show which rules are violated at each world ordered by weighted number 
of rule violations
	6: Show the best worlds at which a formula f is true
 
Preferability among worlds is determined by rule-violations. There are 
three ways of evaluating preferability: If w0 is preferable to w1 then:
1. The rules violated in w0 are a subset of the worlds violated in w2, or  
2. The number of rules violated in w0 is no greater than the number of 
rules violated in w1
3. The weighted rule violations in w0 are no greater than the weighted 
rule violation in w1

Regarding 2: Inferences from R, the user is presented with the following 
options:
1: For some a, b, check if R, a |= b holds with respect to obligation
2: For some a, b, check if R, a |= b holds with respect to permissibility
3: For some a, b check if R |= (a -> b) obtains 
4: Generate each instance of R |= (a -> b) for {a, b | a and b are 
literals obtained from the atoms of R}
5: Generate all entailments of obligation on R (restricted to literals)
6: Generate all entailments of permissibility on R (restricted to 
literals)

For 1, 2, and 3, a and b can be any arbitrary formulas of propositional 
logic. 4, 5, and 6 are limited to literals because generating all 
formulas is impossible and generating such instances for formulas of 
length 1 or 2, is very slow.

As for augmenting R, this can be done in two ways. The first is simply to 
type in a new rule, the second loads a new rule file and combines it with 
the current ruleset to generate a new one. 
 
The Additional Queries were introduced for debugging purposes but the 
user may occasionally find a few of them useful. 
 
_________________________________________________________________________ 
_________________________________________________________________________ 
 
REMARK: Expressing preferences in propositional logic can be a bit 
tricky. For instance, suppose we want to encode the following preference: 
C > T > F. 
This can be expressed in the form of three rules: 
( ,  C) 
( ~C, T) 
(~(T | C), F) 

