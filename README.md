# GeometricDecomposability
A _Macaulay2_ package to check whether an ideal is geometrically vertex decomposable, developed by [Mike Cummings](https://www.math.mcmaster.ca/~cummim5/) and [Adam Van Tuyl](https://ms.mcmaster.ca/~vantuyl/).

For further information, see: [The GeometricDecomposability package for Macaulay2](https://arxiv.org/abs/2211.02471).

## Installation

Using version 1.21 or higher of _Macaulay2_, run the command `loadPackage "GeometricDecomposability"`. 
We recommend using the most recent version of _Macaulay2_.
The warning message that appeared upon loading the package in _Macaulay2_ version 1.21 (which, in most cases, can be safely ignored) has been fixed in version 1.22 of _Maculay2_.

Alternatively, this package can be installed to _Macaulay2_ by copying the file `GeoetricDecomposability.m2` to your working directory from which you launch _Macaulay2_. 
Then in M2, run the command `installPackage "GeometricDecomposability"` and use the package as you would any other. 

After the package is loaded, you can read the documentation by running `viewHelp GeometricDecomposability`, which will open the documentation in your web browser.

## Background

Geometrically vertex decomposable ideals can be viewed as a generalization of the properties of the Stanley-Reisner ideal of a vertex decomposable simplicial complex.
This family of ideals is based upon the geometric vertex decomposition property defined by Knutson, Miller, and Yong [KMY]. 
Klein and Rajchgot then gave a recursive definition for geometrically vertex decomposable ideals in [KR] using this notion.

An unmixed ideal $I$ in a polynomial ring $R$ is geometrically vertex decomposable if it is the zero ideal, the unit ideal, an ideal generated by indeterminates, or if there is a indeterminate $y$ of $R$ such that two ideals $C_{y,I}$ and $N_{y,I}$ constructed from $I$ are both geometrically vertex decomposable.

Observe that a geometrically vertex decomposable ideal is recursively defined. 
The complexity of verifying that an ideal is geometrically vertex decomposable will increase as the number of indeterminates appearing in the ideal increases.

## Acknowledgements 

We thank Sergio Da Silva, Megumi Harada, Patricia Klein, and Jenna Rajchgot for feedback and improvements.
Cummings was partially supported by an NSERC USRA and CGS-M and the Milos Novotny Fellowship. 
Van Tuyl's research is partially supported by NSERC Discovery Grant 2019-05412.

## References

[KMY] Allen Knutson, Ezra Miller, and Alexander Yong. Gröbner Geometry of Vertex Decompositions and of Flagged Tableaux. J. Reine Angew. Math. 630 (2009) 1–31.

[KR] Patricia Klein and Jenna Rajchgot. Geometric Vertex Decomposition and Liaison. Forum Math. Sigma, 9 (2021) e70:1-23.
