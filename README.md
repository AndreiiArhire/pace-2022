# AFC - An Heuristic Solver for the Directed Feedback Vertex Set Problem
This is a an heuristic solver for the directed version of the feedback vertex set problem, used in the Seventh Edition of [Parameterized Algorithms and Computational Experiments](https://pacechallenge.org/). A feedback vertex set of a graph is a set of nodes with the property that every cycle contains at least one vertex from the set i.e the removal of all vertices from a feedback vertex set leads to an acyclic graph. For a brief description of the solver, we refer the following paper ([PDF](https://andrei-arhire.web.app/assets/AFC_SOLVER.pdf)).

## Required
C++ 11 or higher

## How to build
    $ g++ main.cpp -o main

## How to run
    $ ./main graph.in graph.out S 
   
The input graph is given via a Metis Graph file named ```graph.in```. 
The solver will output the solution in ```graph.out```  after ```S``` seconds.  
Every line in the output file will be in the form ```u``` followed by the new line character ```\n```, where ```u``` represents a node contained in the feedback vertex set.

## Authors
 * Andrei Arhire
 * Paul Diac
