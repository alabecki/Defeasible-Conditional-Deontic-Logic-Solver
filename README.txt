Naive Preferences Solver 
_________________________________________________________________________ 
_________________________________________________________________________ 
 
0. Installation
To run the program, Python 3.x a computer must have Python 3.x installed.
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


1. Introduction: 
The program is intended to model expressions and inferences in defeasibly 
conditional deontic logic. It reads sets of rules (R) from text files 
describing defeasible, conditional obligations and then calculates which 
worlds (i.e. truth assignments) are most preferable. Also, for any 
formula f, the best f-worlds may be calculated, which worlds are used as 
a basis for determining which inferences may be true and whether 
additional rules might be implied from those that are given. 
 
World preference is determined in terms of rule violation. For each 
world w let w.F be the set of rules violated in w. The program supports 
three options when determining preference relations between worlds. 
 
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
exceptions:
	(1) The outermost parentheses for rules must be included
	(2) Any parenthese required for understaning the meaning of the
	expression must be included 

Moreover, spacing within a line ignored is ignored. The following rule is 
perfectly acceptable: 

		Example (a   & ~b &c -> p | q |r) 
 
IMPORTANT: Rules and constraints must appear on lines by themselves or 
the program will be able to parse them correctly. Also, the first 
character of a rule line MUST be a “(“, and the first character of a 
constraint line MUST be a “!”.

Rules may be given weights denoting their relative importance, where a 
higher number denotes greater importance or priority. A weight may be 
added to a rule as a float preceded by a '$' sign.
 
		Example (a | c -> ~b)  $2.3 
 
Several example txt. files are included with the program. 
  

2. Commands: 
 
Once a .txt file has been loaded and processed by the program the 
following queries can be made: 
 
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
		implied (user provides new rule (a -> b))
	10:	Add rule to R
	11:	Augment current rules with rules from an additional file
	12:	Additional Queries
	13:	Write data to text-file
	14:	I am done with this file  
 
Most of these commands are self-explanatory. Note, again, that the user 
may choose from 
how worlds are compared to each other. (5) allows the user to check 
whether the inference 
R: a |- b is true, for any two formulas a and b. Where |- is interpreted 
in terms of obligation. 
(6) does the same but with permissibility. (7) checks if a new rule (a -> 
b) is implied by those 
that are already given. Note that (5) will be stronger than (7), in that 
sometimes R: a |- b will be satisfied while (a -> b) will fail. (8) 
allows the user to add an additional rule r to R while (9) allows the 
user to add all rules (and constraints) from a file to those 
that are already in R. (10) presents user with the following queries: 
 
	1: Show the world states at which a given rule is true 
	2: Show the world states at which a given rule is violated 
	3: Show which rules are false at a given world 
	4: Show which rules are verified at a given world 
	5: Show which rules are neutral relative to a given world 
	6: Show the set of domination relations between rules 
	7: Show the body extension of a rule 
	8: Show the head extension of a rule 
	9: Print body of a rule 
	10: Print head of a rule 
	11: Show constraints 
	12: Show weights of rules 
 
Most of these queries were introduced for debugging purposes but the user 
may occasionally 
find a few of them useful. 
 
_____________________________________________________________________ 
_________________________________________________________________________ 
 

REMARK: Expressing preferences in propositional logic can be a bit 
tricky. For instance, suppose we want to encode the following preference: 
C > T > F. 
This can be expressed in the form of three rules: 
( ,  C) 
( ~C, T) 
(~(T | C), F) 

