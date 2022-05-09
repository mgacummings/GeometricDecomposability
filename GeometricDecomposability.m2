-- -*- coding: utf-8 -*-

newPackage(
  "GeometricVertexDecomposition",
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
  HomePage => ""  -- homepage for the package, if one exists, otherwise remove
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
  all(apply(d, i -> (i == d_0)), true)  -- list only contains true values
  )

--------------------------------------------------------------------------------

isGeneratedByIndeterminates = method(TypicalValue => Boolean)
isGeneratedByIndeterminates(Ideal) := I -> (
  -- handle trivial cases
  if I == 0 then return true;
  if I == 1 then return false;

  -- for the nontrivial cases look at the generators
  R := ring I;
  indets := gens R;
  gensI := first entries gens I;
  isSubset(gensI, indets)
  )

--------------------------------------------------------------------------------

oneStepGVD = method(TypicalValue => List)
oneStepGVD(Ideal, RingElement) := (I, y) -> (

  -- set up the ring
  R := ring I;
  indets := gens R;
  indets := switch(0, index y, indets);
  R := QQ[indets, MonomialOrder=>Lex];
  I := sub(I, R);

  -- get initial y-form and Gröbner basis
  inyForm := ideal leadTerm(1,I);
  G := gens gb I;

  squarefree := true;  -- we only care about the GB being squarefree in y
  gensC := {};
  gensN := {};

  for g in (first entries G) do (
    deg := degree(y, g);
    if deg == 0 then (
      gensC := append(gensC, g);
      gensN := append(gensN, g);
      ) else (
      if deg == 1 then (
        gensC := append(gensC, sub(g, {y=>1}));
        ) else squarefree := false;  -- GB not squarefree in y
      )
    )

  C := ideal(gensC);
  N := ideal(gensN);

  -- Klein, Rajchgot. Lemma 2.6.
  if not squarefree then (
    print("Warning: Groebner basis not squarefree in " | toString y);
    return {false, C, N};
    )

  -- check that the intersection holds
  validOneStep := ( intersect(C, N + ideal(y)) == inyForm );

  if not validOneStep then (
    print("Warning: not a valid geometric vertex decomposition");
    return {false, C, N};
    )

  -- check unmixedness of both C and N
  isUnmixedC := isUnmixed C;
  isUnmixedN := isUnmixed N;

  if not (isUnmixedC or isUnmixedN) then (
    print("Warning: neither C nor N are unmixed");
    return {false, C, N};
    ) else (
      if not isUnmixedC then (
        print("Warning: C is not unmixed");
        return {false, C, N};
        )
      if not isUnmixedN then (
        print("Warning: N is not unmixed");
        return {false, C, N};
        )
      )

  -- redefine the ring and substitute C, N into the new ring
  R = (coefficientRing R)[ delete(y, indets) ];  -- notice this ring is defined globally
  C := sub(C, R);
  N := sub(N, R);

  return {true, C, N};
  )

--------------------------------------------------------------------------------

isGVD = method(TypicalValue => Boolean)
isGVD(Ideal) := I -> (

  if I == 0 or I == 1 or (isGeneratedByIndeterminates I) then return true;
  if not (isUnmixed I) then return false;

  -- original code doesn't run this check every time; set up an option for that
  -- Corollary 4.5, Klein and Rajchgot
  if (isHomogeneous I) and not isCM(R/I) then return false;

  -- brute force check of all orders
  for y in (gens R) do (

    oneStep := oneStepGVD(I, y);
    isValid := oneStep_0;
    if not isValid then continue;  -- go back to top of for loop

    CisGVD := isGVD C;
    NisGVD := isGVD N;

    return (CisGVD and NisGVD);
    )

  -- if we are here, no indeterminate worked
  return false;
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



--******************************************************************************
-- Documentation for functions
--******************************************************************************



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

Test///
R = QQ[x,y,z]
I = ideal(x,y)
assert(isGeneratedByIndeterminates == true)
///


Test///
R = QQ[x_1..x_5]
I = ideal(x_1*x_2-x_3*x_4)
assert(isGeneratedByIndeterminates == false)
///


Test///
R = QQ[a..d]
I = ideal 0
assert(isGeneratedByIndeterminates == true)
///


Test///
R = QQ[a..d]
I = ideal 1
assert(isGeneratedByIndeterminates == false)
///

--------------------------------------------------------------------------------
-- Test oneStepGVD
--------------------------------------------------------------------------------

Test///
///

--------------------------------------------------------------------------------
-- Test isGVD
--------------------------------------------------------------------------------

Test///  -- [KR, Example 2.16]
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


end

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--
-- REFERENCES
--
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

-- [CDRV] Michael Cummings, Sergio Da Silva, Jenna Rajchgot, and Adam Van Tuyl. Toric Ideals of Graphs and Geometric Vertex Decomposition. In Preparation.
-- [DH] Sergio Da Silva and Megumi Harada. Regular Nilpotent Hessenberg Varieties, Gröbner Bases, and Toric Degenerations. In preparation.
-- [KR] Patricia Klein and Jenna Rajchgot. Geometric Vertex Decomposition and Liaison. 2021.
