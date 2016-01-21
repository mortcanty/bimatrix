## Algorithmic game theory with Mathematica

Load the Wolfram language script with

<<bimatrix.m

For payoff matrices A and B, display the bimatrix with

BimatrixF[A,B]

Solve the game with

NashEquilbria[A,B] for support enumeration algorithm

NashEquilibria[A,B,Select->One] for Lemke Howson algorithm

NashEquilibria[A,B,Select->s] for symbolic solution, where s 
is a list of numerical substitutions for the symbols in A and B.

