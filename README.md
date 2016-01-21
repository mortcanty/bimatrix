## Algorithmic game theory with Mathematica

Load the Wolfram language script with

<<~/Wolfram/bimatrix.m

For payoff matrices A and B, display the bimatrix with

BimatrixF[A,B]

Solve the game with

NashEquilbria[A,B] for support enumeration algorithm

NashEquilibira[A,B,Select->One] for Lemke Howson algorithm

NashEquilibrium[A,B,Select->s] for symbolic solution, where s 
is a list of numerical substitutions ffor the symbols in A and B.

