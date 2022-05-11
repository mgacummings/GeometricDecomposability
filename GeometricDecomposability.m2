-- -*- coding: utf-8 -*-

newPackage(
  "GeometricDecomposability",
  Version => "0.1",
  Date => "April 9, 2022",
  Headline => "A package to check whether ideals are geometrically vertex decomposable",
  Authors => {
    {
    Name => "Mike Cummings",
    Email => "cummim5@mcmaster.ca"
    },
    {
    Name => "Adam Van Tuyl",
    Email => "vantuyl@math.mcmaster.ca",
    HomePage => "https://ms.mcmaster.ca/~vantuyl/"
    }
  }
  Keywords => {"Algebraic Geometry"},  -- keywords from the headings here: http://www2.macaulay2.com/Macaulay2/doc/Macaulay2-1.17/share/doc/Macaulay2/Macaulay2Doc/html/_packages_spprovided_spwith_sp__Macaulay2.html
    PackageImports => {"PrimaryDecomposition", "Depth"},  -- I don't think these need to be imported for the user? Hence PackageImports and not PackageExports
  HomePage => ""  -- homepage for the package, if one exists, otherwise leave blank or remove
  )

export {  -- list of functions which will be visible to the user
  isUnmixed,
  isGeneratedByIndeterminates,
  oneStepGVD,
  isGVD
  };

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--
-- FUNCTIONS
--
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

isUnmixed = method(TypicalValue => Boolean)
isUnmixed(Ideal) := I -> (
  R := ring I;
  D := primaryDecomposition I;
  d := apply(D, i -> dim(R/i));
  all(apply(d, i -> (i == d_0)), i -> i)  -- list only contains true values
  )

--------------------------------------------------------------------------------

isGeneratedByIndeterminates = method(TypicalValue => Boolean)
isGeneratedByIndeterminates(Ideal) := I -> (
  -- handle trivial cases
  if I == 0 then return true;
  if I == 1 then return false;

  -- look at the generators for the nontrivial cases
  R := ring I;
  indeterminates := gens R;
  gensI := first entries gens I;
  isSubset(gensI, indeterminates)
  )

--------------------------------------------------------------------------------

oneStepGVD = method(TypicalValue => List)
oneStepGVD(Ideal, RingElement) := (J, z) -> (

  -- set up the ring
  indeterminates := switch(0, index z, gens ring J);
  R := QQ[indeterminates, MonomialOrder=>Lex];
  I := sub(J, R);
  y := sub(z, R);

  -- get the ideal of initial y-form and a Gröbner basis
  inyForm := ideal leadTerm(1,I);
  G := first entries gens gb I;

  gensN := delete(0, apply(G, g -> isInN(g, y)));
  gensC := apply(G, g -> isInC(g, y));
  squarefree := (number(gensC, i -> (i === false)) == 0);  -- squarefree is true iff number of `false` in gensC is 0

  CyI := ideal(gensC);
  NyI := ideal(gensN);

  -- [KR, Lemma 2.6]
  if not squarefree then (
    print("Warning: Gröbner basis not squarefree in " | toString y);
    return {false, CyI, NyI};
    );

  -- check that the intersection holds
  validOneStep := ( intersect(CyI, NyI + ideal(y)) == inyForm );

  if not validOneStep then (
    print("Warning: not a valid geometric vertex decomposition");
    return {false, CyI, NyI};
    );

  -- check unmixedness of both CyI and NyI
  isUnmixedC := isUnmixed CyI;
  isUnmixedN := isUnmixed NyI;

  if not (isUnmixedC or isUnmixedN) then (
    print("Warning: neither CyI nor NyI are unmixed");
    return {false, CyI, NyI};
    )
  else (
    if not isUnmixedC then (
      print("Warning: CyI is not unmixed");
      return {false, CyI, NyI};
      );
    if not isUnmixedN then (
      print("Warning: NyI is not unmixed");
      return {false, CyI, NyI};
      )
    );

  -- redefine the ring and substitute CyI, NyI into the new ring
  R = (coefficientRing R)[ delete(y, indeterminates) ];
  C := sub(CyI, R);
  N := sub(NyI, R);

  return {true, C, N};
  );

--------------------------------------------------------------------------------

CyI = method(TypicalValue => Ideal)
CyI(Ideal, RingElement) := (I, y) -> oneStepGVD(I, y)_1;

----------------------------------------

NyI = method(TypicalValue => Ideal)
NyI(Ideal, RingElement) := (I, y) -> oneStepGVD(I, y)_2;

--------------------------------------------------------------------------------

isGVD = method(TypicalValue => Boolean)
isGVD(Ideal, String, Boolean) := (I, checkCM, homogeneous) -> (

  print I;  --remove this later?

  if I == 0 or I == 1 or (isGeneratedByIndeterminates I) then return true;
  if not (isUnmixed I) then return false;

  -- Corollary 4.5, Klein and Rajchgot: homogeneous and not Cohen-Macaulay implies not GVD
  if (checkCM == "once" or checkCM == "always") then (
    if (not homogeneous) then homogeneous := isHomogeneous I;
    if homogeneous then (
      if (not isCM(R/I)) then return false;
      )
    );
  if checkCM == "once" then checkCM := "never";

  -- check all options for y until one works
  for y in (gens R) do (

    oneStep := oneStepGVD(I, y);
    isValid := oneStep_0;
    if not isValid then continue;  -- go back to top of for loop

    C := oneStep_1;
    N := oneStep_2;

    CisGVD := isGVD(C, checkCM=>checkCM, homogeneous=>homogeneous);
    NisGVD := isGVD(N, checkCM=>checkCM, homogeneous=>homogeneous);

    if (CisGVD and NisGVD) then return true;
    );

  -- if we are here, no choice of y worked
  return false;
  )

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

--** FUNCTIONS (HIDDEN FROM USER)

isInN = method()
isinN(RingElement, RingElement) := (f, y) -> (
  -- f is a polynomial, y an indeterminate
  if degree(y, f) == 0 then return f else return 0;  -- 0 is a temp value which we remove immediately, used as opposed to null
  )

isInC = method()
isInC(RingElement, RingElement) := (f, y) -> (
  -- f is a polynomial, y an indeterminate
  if degree(y, f) == 0 then return f;
  if degree(y, f) == 1 then return getQ(f, y) else return false;  -- returns false if not squarefree
  )

getQ = method()
getQ(RingElement, RingElement) := (f, y) -> (
  -- f is of the form yq+r, return q
  r := sub(f, y=>0);
  yq := f - r;
  return sub(yq, y=>1);
  )

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--
-- DOCUMENTATION
--
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

beginDocumentation()

--******************************************************************************
-- Documentation for package
--******************************************************************************

doc///
    Key
        GeometricDecomposability

    Headline
        A package to check whether ideals are geometrically vertex decomposable

    Description
        Text

            This package includes routines to check whether an ideal is
            geometrically vertex decomposable. The notion of geometric vertex
            decomposability can be considered as a generalization of the
            properties of the Stanley-Reisner ideal of a vertex decomposable
            simplicial complex.

            References:

            [CDRV] Michael Cummings, Sergio Da Silva, Jenna Rajchgot, and Adam Van
            Tuyl. Toric Ideals of Graphs and Geometric Vertex Decomposition. In
            Preparation.

            [DH] Sergio Da Silva and Megumi Harada. Regular Nilpotent Hessenberg
            Varieties, Gröbner Bases, and Toric Degenerations. In preparation.

            [KMY] Allen Knutson, Ezra Miller, and Alexander Yong. Gröbner geometry
            of vertex decompositions and of flagged tableaux. J. Reine Angew. Math.,
            630:1--31, 2009.

            [KR] Patricia Klein and Jenna Rajchgot. Geometric Vertex Decomposition
            and Liaison. Forum of Math, Sigma, 9(70), 2021.
///

--******************************************************************************
-- Documentation for functions
--******************************************************************************

doc///
    Key
        isUnmixed
        (isUnmixed, Ideal)
///


doc///
    Key
        isGeneratedByIndeterminates
        (isGeneratedByIndeterminates, Ideal)
///


doc///
    Key
        oneStepGVD
        (oneStepGVD, Ideal, RingElement)
///


doc///
    Key
        CyI
        (CyI, Ideal, RingElement)
///


doc///
    Key
        NyI
        (NyI, Ideal, RingElement)
///


doc///
    Key
        isGVD
        (isGVD, Ideal)
///

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--
-- TESTS
--
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Test isUnmixed
--------------------------------------------------------------------------------

Test///
///

--------------------------------------------------------------------------------
-- Test isGeneratedByIndeterminates
--------------------------------------------------------------------------------

TEST///
R = QQ[x,y,z]
I = ideal(x,y)
assert(isGeneratedByIndeterminates == true)
///


TEST///
R = QQ[x_1..x_5]
I = ideal(x_1*x_2-x_3*x_4)
assert(isGeneratedByIndeterminates == false)
///


TEST///
R = QQ[a..d]
I = ideal 0
assert(isGeneratedByIndeterminates == true)
///


TEST///
R = QQ[a..d]
I = ideal 1
assert(isGeneratedByIndeterminates == false)
///

--------------------------------------------------------------------------------
-- Test oneStepGVD
--------------------------------------------------------------------------------

TEST///
///

--------------------------------------------------------------------------------
-- Test isGVD
--------------------------------------------------------------------------------

TEST///  -- [KR, Example 2.16]
R = QQ[x,y,z,w,r,s]
I = ideal(y*(z*s - x^2), y*w*r, w*r*(z^2 + z*x + w*r + s^2))
assert(isGVD I == true)
///


TEST///  -- Toric ideal of the complete bipartite graph K_{5,3}; GVD by a result from [CDRV]
loadPackage "Quasidegrees"
R = QQ[e_1..e_15]
A = matrix{
  {1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0},
  {0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0},
  {0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0},
  {0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0},
  {0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1},
  {1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1}
}
I = toricIdeal(A, R)
assert(isGVD I == true)
///


TEST///  -- Toric ideal of the graph constructed by connecting two triangles by a bridge of length 2
loadPackage "Quasidegrees"
R = QQ[e_1..e_8]
A = matrix{
  {1, 0, 1, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 0, 1, 0, 0},
  {0, 0, 0, 1, 0, 0, 1, 0},
  {1, 0, 0, 0, 1, 0, 0, 0},
  {0, 1, 0, 0, 0, 0, 0, 1},
  {0, 0, 1, 1, 1, 0, 0, 0},
  {0, 0, 0, 0, 0, 1, 1, 1}
}
I = toricIdeal(A, R)
assert(isGVD I == false)
///


TEST///  -- Hessenberg patch ideal corresponding to the $w_0$ chart and Hessenberg function h=(2,3,4,5,6,6), GVD by a result from [DH]
R = QQ[x_11..x_15, x_21..x_24, x_31..x_33, x_41, x_42, x_51]
A = matrix{
  {x_11, x_12, x_13, x_14, x_15, 1},
  {x_21, x_22, x_23, x_24, 1, 0},
  {x_31, x_32, x_33, 1, 0, 0},
  {x_41, x_42, 1, 0, 0, 0},
  {x_51, 1, 0, 0, 0, 0},
  {1, 0, 0, 0, 0, 0}
}
N = matrix{
  {0, 1, 0, 0, 0, 0},
  {0, 0, 1, 0, 0, 0},
  {0, 0, 0, 1, 0, 0},
  {0, 0, 0, 0, 1, 0},
  {0 ,0, 0, 0, 0, 1},
  {0, 0, 0, 0, 0, 0}
}
X = inverse(A) * N * A
I = ideal( X_(2,0), X_(3,0), X_(3,1), X_(4,0), X_(4,1), X_(4,2), X_(5,0), X_(5,1), X_(5,2), X_(5,3) )
assert(isGVD I == true)
///


TEST///  -- not GVD, w = (2,1,4,3), h = (2,3,4,4)
R = QQ[x_11, x_31..x_33, x_41, x_42]
A = matrix{
  {x_11, 1, 0, 0},
  {1, 0, 0, 0},
  {x_31, x_32, x_33, 1},
  {x_41, x_42, 1, 0}
}
N = matrix{
  {0, 1, 0, 0},
  {0, 0, 1, 0},
  {0, 0, 0, 1},
  {0, 0, 0, 0}
}
X = inverse(A) * N * A
I = ideal(X_(2,0), X_(3,0), X_(3,1))
assert(isGVD I == false)
///


end--

OUTDATED CODE

from oneStepGVD

for g in (first entries G) do (
  deg := degree(y, g);
  if deg == 0 then (
    gensC := append(gensC, g);
    gensN := append(gensN, g);
    )
    else (
      if deg == 1 then (
        gensC := append(gensC, sub(g, {y=>1}));
        ) else squarefree := false;  -- GB not squarefree in y
    )
  );
