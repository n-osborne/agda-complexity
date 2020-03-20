# agda-complexity

This project aims at expressing time complexity of simple algorithm
using Agda type system (typically insertion sort).

## Cost monad

In order to keep track of the number of elementaries computation, I
use what I call a *cost monad* (``CostMonad.agda``). This is inspired
by Anders Danielsson's Thunk monad [1](http://www.cse.chalmers.se/~nad/publications/danielsson-popl2008.pdf).

The general idea is to use a monad to annotate computations with their
cost. The *bind* operator then add up the cost of the computations.

The main difference with Danielsson is that I don't use ticks inside
the algorithm. Instead, I propose to use lifted operations. In doing
so, I hope to be able to build a framework to define different cost
models. The ``lift`` operation allows to choose which computation are
counted as atomic operation.

At this point, we are able to express the linear cost of *foldr* and
*map* combinators on Vectors.

## Filter and Big-O notation

In order to express Big-O notation, I follow [2]. I define the notion
of Filter in ``Filter.agda``. The main idea is that a Filter has the
same type as a Quantifier, which is what we want in order to capture
Big-O notation (for all the x that are bigger than c).

I choose to define Filter as a special subset of a Poset rather than
with Powersets like [2] so that I can use the partial order relation
of the agda standard library. I don't know yet if this is a good idea
w.r.t the definition of Big-O notation.

Then, the definition of BigO is relatively straightforward. This is defined
in ``BigO.agda``. So far, I have just the trivial proof that f ∈ O(f).

## References

[1] Nils Anders Danielsson, *Lightweight Semiformal Time Complexity Analysis for Purely Functional Data Structures*
[2] Armaël Guéneau, Arthur Charguéraud, François Pottier, *A Fistful of Dollars: Formalizing Asymptotic Complexity Claims via Deductive Program Verification*
