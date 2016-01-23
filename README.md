## Algorithmic game theory with Mathematica on the Raspberry Pi

### Installation

Clone the repository to a convenient location, e.g., ~/Wolfram

On Raspbian or Ubuntu run

    sudo apt-get update && sudo apt-get install lrslib

### Run the software 

Start Mathematica

Load the Wolfram language game theory script with

    <<Wolfram/src/bimatrix.m
    
For payoff matrices A and B, display the bimatrix with

    BimatrixForm[A,B]

Solve the game with, eg., 

    NashEquilbria[A,B] 

for the support enumeration algorithm

    NashEquilibria[A,B,Select->One] 

for the Lemke Howson algorithm

    NashEquilibria[A,B,Select->All] f

for complete vertex enumeration.

For symbolic payoff matrices As and Bs, solve the game symbolicaly with

    NashEquilibria[As,Bs,Symbolic->s]

where s is a list of numerical substitutions for all of the symbols on As and Bs.

There are many other forms, including normal form perfect equilibria, evolutionarily
stable equilibria, zero-sum games, maximal Nash subsets, ...

Get help with

    ?NashEquilibria
    ?Select
