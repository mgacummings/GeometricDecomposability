indetOrder-- -*- coding: utf-8 -*-

newPackage(
  "GeometricDecomposability",
  Version => "0.2",
  Date => "May 25, 2022",
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
  },
  Keywords => {"Algebraic Geometry", "Commutative Algebra"},  -- keyword(s) from the headings here: http://www2.macaulay2.com/Macaulay2/doc/Macaulay2-1.17/share/doc/Macaulay2/Macaulay2Doc/html/_packages_spprovided_spwith_sp__Macaulay2.html
  PackageImports => {"PrimaryDecomposition", "Depth"},  -- I don't think these need to be imported for the user? Hence PackageImports and not PackageExports
  HomePage => ""  -- homepage for the package, if one exists, otherwise leave blank/remove
  )

export {
  -- functions
  "CyI",
  "findLexGVDOrder",
  "getGVDIdeal",
  "isGeneratedByIndeterminates",
  "isGVD",
  "isLexGVD",
  "isUnmixed",
  "isWeaklyGVD",
  "NyI",
  "oneStepGVD",

  -- options
  "CheckCM",
  "CheckDegenerate",
  "IsIdealHomogeneous",
  "IsIdealUnmixed",
  "RandomSeed",
  "ShowOutput"
  };

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--
-- FUNCTIONS
--
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------

CyI = method(TypicalValue => Ideal)
CyI(Ideal, RingElement) := (I, y) -> (oneStepGVD(I, y))_1;

--------------------------------------------------------------------------------

findLexGVDOrder = method(TypicalValue => List, Options => {RandomSeed => 1})
findLexGVDOrder(Ideal) := opts -> I -> (
  -- restrict to the ring of indeterminates appearing in I by [CDRV, tensor product result]
  setRandomSeed opts.RandomSeed;
  possibleOrders := random permutations support I;

  for indetOrder in possibleOrders do (
    if isLexGVD(I, indetOrder, ShowOutput=>false) then return {true, indetOrder};
    );
  return {false};   -- no order worked
  )

--------------------------------------------------------------------------------

getGVDIdeal = method(TypicalValue => List)
getGVDIdeal(Ideal, List) := (I, L) -> (
  CNs := new HashTable from {
    "C" => CyI,
    "N" => NyI
    };
  return accumulate( (i, j) -> CNs#(j_0)(i, j_1) , prepend(I, L) );  -- last entry is the desired ideal
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
  return isSubset(gensI, indeterminates);
  )

--------------------------------------------------------------------------------

-- [KR, Definition 2.7]
isGVD = method(TypicalValue => Boolean, Options => {ShowOutput => true, IsIdealUnmixed => false, CheckCM => "once", IsIdealHomogeneous => false})
isGVD(Ideal) := opts -> I -> (
  R := ring I;
  printIf(opts.ShowOutput, toString I);  --remove this later?

  if I == 0 then (printIf(opts.ShowOutput, "-- zero ideal"); return true);
  if I == 1 then (printIf(opts.ShowOutput, "-- unit ideal"); return true);
  if (isGeneratedByIndeterminates I) then (printIf(opts.ShowOutput, "-- generated by indeterminates"); return true);

  if not opts.IsIdealUnmixed then (
    if not (isUnmixed I) then (printIf(opts.ShowOutput, "-- ideal is not unmixed"); return false);
    );

  x := opts.IsIdealHomogeneous or isHomogeneous(I);
  if opts.CheckCM == "once" or opts.CheckCM == "always" then (
    if x then (if (not isCM(R/I)) then return false;);
    );

  CMTable := new HashTable from {
    "always" => "always",
    "once" => "never",
    "never" => "never"
    };

  -- check all options for y until one works
  for y in (support I) do (

    printIf(opts.ShowOutput, "-- decomposing with respect to " | toString y);

    oneStep := oneStepGVD(I, y, ShowOutput=>opts.ShowOutput);
    isValid := oneStep_0;
    if not isValid then continue;  -- go back to top of for loop

    C := oneStep_1;
    N := oneStep_2;

    printIf(opts.ShowOutput, "-- C = " | toString C);
    printIf(opts.ShowOutput, "-- N = " | toString N);

    CisGVD := isGVD(C, ShowOutput=>opts.ShowOutput, IsIdealUnmixed=>true, CheckCM=>CMTable#(opts.CheckCM), IsIdealHomogeneous=>x);
    NisGVD := isGVD(N, ShowOutput=>opts.ShowOutput, IsIdealUnmixed=>true, CheckCM=>CMTable#(opts.CheckCM), IsIdealHomogeneous=>x);

    if (CisGVD and NisGVD) then return true;
    );

  -- if we are here, no choice of y worked
  return false;
  )

--------------------------------------------------------------------------------

-- [KR, Definition 2.11]
isLexGVD = method(TypicalValue => Boolean, Options => {ShowOutput => true, IsIdealUnmixed => false, CheckCM => "once", IsIdealHomogeneous => false})
isLexGVD(Ideal, List) := opts -> (I, indetOrder) -> (
  R := ring I;
  printIf(opts.ShowOutput, toString I);  --remove this later?

  if I == 0 then (printIf(opts.ShowOutput, "-- zero ideal"); return true);
  if I == 1 then (printIf(opts.ShowOutput, "-- unit ideal"); return true);
  if (isGeneratedByIndeterminates I) then (printIf(opts.ShowOutput, "-- generated by indeterminates"); return true);

  supportIndets := support I;
  trimmedOrder := select(indetOrder, i -> member(sub(i, R), supportIndets));

  if not opts.IsIdealUnmixed then (
    if not (isUnmixed I) then (printIf(opts.ShowOutput, "-- ideal is not unmixed"); return false);
    );

  x := opts.IsIdealHomogeneous or isHomogeneous(I);
  if opts.CheckCM == "once" or opts.CheckCM == "always" then (
    if x then (if (not isCM(R/I)) then return false;);
    );

  CMTable := new HashTable from {
    "always" => "always",
    "once" => "never",
    "never" => "never"
    };

  -- check next indeterminate in list
  y := first trimmedOrder;
  remainingOrder := take(trimmedOrder, {1, #trimmedOrder});

  printIf(opts.ShowOutput, "-- decomposing with respect to " | toString y);
  oneStep := oneStepGVD(I, y, ShowOutput=>opts.ShowOutput);
  isValid := oneStep_0;
  if not isValid then return false;  -- order didn't work

  C := oneStep_1;
  N := oneStep_2;

  printIf(opts.ShowOutput, "-- C = " | toString C);
  printIf(opts.ShowOutput, "-- N = " | toString N);

  CisGVD := isLexGVD(C, remainingOrder, ShowOutput=>opts.ShowOutput, IsIdealUnmixed=>true, CheckCM=>CMTable#(opts.CheckCM), IsIdealHomogeneous=>x);
  NisGVD := isLexGVD(N, remainingOrder, ShowOutput=>opts.ShowOutput, IsIdealUnmixed=>true, CheckCM=>CMTable#(opts.CheckCM), IsIdealHomogeneous=>x);

  return (CisGVD and NisGVD);
  )

--------------------------------------------------------------------------------

isUnmixed = method(TypicalValue => Boolean)
isUnmixed(Ideal) := I -> (
  R := ring I;
  D := primaryDecomposition I;
  d := apply(D, i -> dim(R/i));
  return all(apply(d, i -> (i == d_0)), i -> i);  -- list only contains true values
  )

--------------------------------------------------------------------------------

-- [KR, Definition 4.6]
isWeaklyGVD = method(TypicalValue => Boolean, Options => {IsIdealUnmixed => false, ShowOutput => true})
isWeaklyGVD(Ideal) := opts -> I -> (
  R := ring I;
  printIf(opts.ShowOutput, toString I);  --remove this later?

  if I == 0 then (printIf(opts.ShowOutput, "-- zero ideal"); return true);
  if I == 1 then (printIf(opts.ShowOutput, "-- unit ideal"); return true);
  if (isGeneratedByIndeterminates I) then (printIf(opts.ShowOutput, "-- generated by indeterminates"); return true);

  if not opts.IsIdealUnmixed then (
    if not (isUnmixed I) then (printIf(opts.ShowOutput, "-- ideal is not unmixed"); return false);
    );

  -- check all options for y until one works
  for y in (support I) do (

    printIf(opts.ShowOutput, "-- decomposing with respect to " | toString y);

    oneStep := oneStepGVD(I, y, CheckDegenerate=>true, ShowOutput=>opts.ShowOutput);
    isValid := oneStep_0;
    if not isValid then continue;  -- go back to top of for loop
    C := oneStep_1;
    N := oneStep_2;
    degenerateOneStep := (oneStep_3 == "degenerate");

    printIf(opts.ShowOutput, "-- C = " | toString C);
    printIf(opts.ShowOutput, "-- N = " | toString N);
    printIf(opts.ShowOutput, "-- form a " | oneStep_3 | " geometric vertex decomposition");

    if degenerateOneStep then (
      -- degenerate case
      if isWeaklyGVD(N, IsIdealUnmixed=>true, ShowOutput=>opts.ShowOutput) then return true else continue;

      ) else (
      -- nondegenerate case
      if not (radical(N, Unmixed=>true) == N and isCM(ring N/N)) then continue;
      if isWeaklyGVD(C, IsIdealUnmixed=>true, ShowOutput=>opts.ShowOutput) then return true else continue;
      )
    );
  -- if we are here, no choice of y worked
  return false;
  )

--------------------------------------------------------------------------------

NyI = method(TypicalValue => Ideal)
NyI(Ideal, RingElement) := (I, y) -> (oneStepGVD(I, y))_2;

--------------------------------------------------------------------------------

-- [KMY, Theorem 2.1]
oneStepGVD = method(TypicalValue => List, Options => {ShowOutput => true, CheckDegenerate => false})
oneStepGVD(Ideal, RingElement) := opts -> (I, y) -> (

  -- set up the rings
  indeterminates := switch(0, index y, gens ring y);
  remainingIndets := drop(gens ring y, {index y, index y});
  cr := coefficientRing ring I;

  givenRing := ring I;
  initYFormRing := cr[indeterminates, MonomialOrder=>ProductOrder{1, #indeterminates - 1}];
  lexRing := cr[indeterminates, MonomialOrder=>Lex];
  contractedRing := cr[remainingIndets];

  -- get the ideal of initial y-forms using the product order
  I = sub(I, initYFormRing);
  y = sub(y, initYFormRing);
  inyFormIdeal := ideal leadTerm(1,I);

  -- pull evertying into a ring using lex
  use lexRing;
  I = sub(I, lexRing);
  y = sub(y, lexRing);
  inyForm := sub(inyFormIdeal, lexRing);
  G := first entries gens gb I;

  -- get N_{y,I}
  gensN := delete(0, apply(G, g -> isInN(g, y)));
  NyI := ideal(gensN);

  -- get C_{y, I} and determine whether the GB is squarefree in y
  gensC := delete(true, flatten(apply(G, g -> isInC(g, y))));
  squarefree := (number(gensC, i -> (i === false)) == 0);  -- squarefree is true iff number of `false` in gensC is 0
  CyI := ideal(delete(false, gensC));

  -- [KR, Lemma 2.6]
  if not squarefree then (
    printIf(opts.ShowOutput, "Warning: Gröbner basis not squarefree in " | toString y);
    use givenRing;
    return {false, CyI, NyI};
    );

  -- check that the intersection holds
  -- sub CyI, NyI into lexRing in case either is zero or unit ideal
  validOneStep := ( intersect( sub(CyI, lexRing), sub(NyI, lexRing) + ideal(y) ) == inyForm );

  use givenRing;
  C := sub(CyI, givenRing);
  N := sub(NyI, givenRing);

  if not validOneStep then (
    printIf(opts.ShowOutput, "Warning: not a valid geometric vertex decomposition");
    return {false, C, N};
    );

  -- check unmixedness of both CyI and NyI
  isUnmixedC := isUnmixed C;
  isUnmixedN := isUnmixed N;

  if not isUnmixedC then (
    printIf(opts.ShowOutput, "Warning: CyI is not unmixed");
    );
  if not isUnmixedN then (
    printIf(opts.ShowOutput, "Warning: NyI is not unmixed");
    );
  if not (isUnmixedC and isUnmixedN) then (
    return {false, CyI, NyI};
    );

  if opts.CheckDegenerate then (
    -- degenerate if C == 1 or radical C == radical N
    if C == 1 then return {true, C, N, "degenerate"};

    radC := radical(C, Unmixed=>true);
    radN := radical(N, Unmixed=>true);
    if (radC == radN) then return {true, C, N, "degenerate"};

    -- if we are here, we are nondegenerate
    return {true, C, N, "nondegenerate"};
    );
  return {true, C, N};
  )

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

--** FUNCTIONS (HIDDEN FROM USER)

isInC = method(TypicalValue => List)
isInC(RingElement, RingElement) := (f, y) -> (
  -- f is a polynomial, y an indeterminate
  if degree(y, f) == 0 then return {true, f};
  if degree(y, f) == 1 then return {true, getQ(f, y)};
  return {false, getQ(f, y)};
  )


isInN = method()
isInN(RingElement, RingElement) := (f, y) -> (
  -- f is a polynomial, y an indeterminate
  if degree(y, f) == 0 then return f else return 0;  -- 0 is a temp value which we remove immediately, used as opposed to null
  )


getQ = method(TypicalValue => RingElement)
getQ(RingElement, RingElement) := (f, y) -> (
  -- f is of the form q*y^d+r, return q
  r := sub(f, y=>0);
  qy := f - r;
  return sub(qy, y=>1);
  )


printIf = method()
  printIf(Boolean, String) := (bool, str) -> (
    if bool then print str;
    )


ringWeights = method(TypicalValue => List)
ringWeights(RingElement) := y -> (
  -* y will be weighted 10, the rest of the indeterminates will be weighted 0 *-

  R := ring y;
  indets := gens R;
  weights := append( splice{ (#indets-1):0 } , 10);
  switch(index y, -1, weights)
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
    Node
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

                [SM] Saremi, H., Mafi, A. Unmixedness and arithmetic properties of
                matroidal ideals. Arch. Math. 114:299–304, 2020.
                https://doi.org/10.1007/s00013-019-01402-w.
///

--******************************************************************************
-- Documentation for functions
--******************************************************************************


doc///
    Node
        Key
            CyI
            (CyI, Ideal, RingElement)
///


doc///
    Node
        Key
            findLexGVDOrder
            (findLexGVDOrder, Ideal)
            [findLexGVDOrder, RandomSeed]
///


doc///
    Node
        Key
            getGVDIdeal
            (getGVDIdeal, Ideal, List)
///


doc///
    Node
        Key
            isGeneratedByIndeterminates
            (isGeneratedByIndeterminates, Ideal)
///


doc///
    Node
        Key
            isGVD
            (isGVD, Ideal)
            [isGVD, CheckCM]
            [isGVD, IsIdealHomogeneous]
            [isGVD, IsIdealUnmixed]
            [isGVD, ShowOutput]
        Usage
            isGVD I
        Inputs
            I:Ideal
            ShowOutput:Boolean
                if output should be printed or suppressed, default value: true
            CheckCM:String
                whether to check that the ideal is GVD using the result of [KR, Corollary 4.5] "once" (default, only for the ideal given in the input and none of the following C, N ideals), "always", or "never"
            IsIdealHomogeneous:Boolean
                if the given ideal is homogeneous, if known. If not, it is checked if the Cohen-Macaulay check runs
///


doc///
    Node
        Key
            isLexGVD
            (isLexGVD, Ideal, List)
            [isLexGVD, CheckCM]
            [isLexGVD, IsIdealHomogeneous]
            [isLexGVD, IsIdealUnmixed]
            [isLexGVD, ShowOutput]
        Usage
            isLexGVD(I, order)
        Inputs
            I:Ideal
            ShowOutput:Boolean
                if output should be printed or suppressed, default value: true
            CheckCM:String
                whether to check that the ideal is GVD using the result of [KR, Corollary 4.5] "once" (default, only for the ideal given in the input and none of the following C, N ideals), "always", or "never"
            IsIdealHomogeneous:Boolean
                if the given ideal is homogeneous, if known. If not, it is checked if the Cohen-Macaulay check runs
///


doc///
    Node
        Key
            isUnmixed
            (isUnmixed, Ideal)
///


doc///
    Node
        Key
            isWeaklyGVD
            (isWeaklyGVD, Ideal)
            [isWeaklyGVD, IsIdealUnmixed]
            [isWeaklyGVD, ShowOutput]
        Usage
            isWeaklyGVD I
        Inputs
            I:Ideal
            ShowOutput:Boolean
                if output should be printed or suppressed, default value: true
///


doc///
    Node
        Key
            NyI
            (NyI, Ideal, RingElement)
///


doc///
    Node
        Key
            oneStepGVD
            (oneStepGVD, Ideal, RingElement)
            [oneStepGVD, ShowOutput]
            [oneStepGVD, CheckDegenerate]
///


undocumented { "CheckDegenerate", "CheckCM", "IsIdealHomogeneous", "IsIdealUnmixed", "RandomSeed", "ShowOutput" }

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--
-- TESTS
--
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Test CyI  --** note to self: just re-use the test cases from oneStepGVD
--------------------------------------------------------------------------------


--TEST///
--///


--------------------------------------------------------------------------------
-- Test findLexGVDOrder
--------------------------------------------------------------------------------


TEST///
R = QQ[x,y];
I = ideal(x^2 - y^2);
assert(findLexGVDOrder I == {false})
///


TEST///
R = QQ[x..z];
I = ideal(x-y, x-z);
assert( findLexGVDOrder(I, RandomSeed=>11) == {true, {z, y, x}} )
///


--------------------------------------------------------------------------------
-- Test getGVDIdeal
--------------------------------------------------------------------------------


--TEST///
--///


--------------------------------------------------------------------------------
-- Test isGeneratedByIndeterminates
--------------------------------------------------------------------------------


TEST///
R = QQ[x,y,z];
I = ideal(x,y);
assert(isGeneratedByIndeterminates I)
///


TEST///
R = QQ[x_1..x_5];
I = ideal(x_1*x_2-x_3*x_4);
assert(not isGeneratedByIndeterminates I)
///


TEST///
R = QQ[a..d];
I = ideal 0;
assert(isGeneratedByIndeterminates I)
///


TEST///
R = QQ[a..d];
I = ideal 1;
assert(not isGeneratedByIndeterminates I)
///


--------------------------------------------------------------------------------
-- Test isGVD
--------------------------------------------------------------------------------


TEST///  -- [KR, Example 2.16]
R = QQ[x,y,z,w,r,s];
I = ideal(y*(z*s - x^2), y*w*r, w*r*(z^2 + z*x + w*r + s^2));
assert(isGVD(I, ShowOutput=>false))
///


TEST///  -- [KR, Example 4.10]
R = QQ[x,y,z,w,r,s];
I = ideal(y*(z*s - x^2), y*w*r, w*r*(x^2+ z^2 + s^2 + w*r));
assert(not isGVD(I, ShowOutput=>false))
///


TEST///  -- Toric ideal of the complete bipartite graph K_{3,2}; GVD by a result from [CDRV]
loadPackage "Quasidegrees";
R = QQ[e_1..e_6];
A = matrix{
  {1,0,0,1,0,0},
  {0,1,0,0,1,0},
  {0,0,1,0,0,1},
  {1,1,1,0,0,0},
  {0,0,0,1,1,1}
  };
I = toricIdeal(A, R);
assert(isGVD(I, ShowOutput=>false))
///


TEST///  -- Toric ideal of the graph constructed by connecting two triangles by a bridge of length 2
loadPackage "Quasidegrees";
R = QQ[e_1..e_8];
A = matrix{
  {1, 0, 1, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 0, 1, 0, 0},
  {0, 0, 0, 1, 0, 0, 1, 0},
  {1, 0, 0, 0, 1, 0, 0, 0},
  {0, 1, 0, 0, 0, 0, 0, 1},
  {0, 0, 1, 1, 1, 0, 0, 0},
  {0, 0, 0, 0, 0, 1, 1, 1}
  };
I = toricIdeal(A, R);
assert(not isGVD(I, ShowOutput=>false))
///


TEST///  -- Hessenberg patch ideal corresponding to the $w_0$ chart and Hessenberg function h=(2,3,4,5,6,6), GVD by a result from [DH]
R = QQ[x_11..x_15, x_21..x_24, x_31..x_33, x_41, x_42, x_51];
A = matrix{
  {x_11, x_12, x_13, x_14, x_15, 1},
  {x_21, x_22, x_23, x_24, 1, 0},
  {x_31, x_32, x_33, 1, 0, 0},
  {x_41, x_42, 1, 0, 0, 0},
  {x_51, 1, 0, 0, 0, 0},
  {1, 0, 0, 0, 0, 0}
  };
N = matrix{
  {0, 1, 0, 0, 0, 0},
  {0, 0, 1, 0, 0, 0},
  {0, 0, 0, 1, 0, 0},
  {0, 0, 0, 0, 1, 0},
  {0 ,0, 0, 0, 0, 1},
  {0, 0, 0, 0, 0, 0}
  };
X = inverse(A) * N * A;
I = ideal( X_(2,0), X_(3,0), X_(3,1), X_(4,0), X_(4,1), X_(4,2), X_(5,0), X_(5,1), X_(5,2), X_(5,3) );
assert(isGVD(I, ShowOutput=>false))
///


TEST///  -- not GVD, w = (1,3,2,4), h = (3,3,4,4)
R = QQ[x_21, x_22, x_31, x_41..x_43];
A = matrix{
  {1, 0, 0, 0},
  {x_21, x_22, 1, 0},
  {x_31, 1, 0, 0},
  {x_41, x_42, x_43, 1}
  };
N = matrix{
  {0, 1, 0, 0},
  {0, 0, 1, 0},
  {0, 0, 0, 1},
  {0, 0, 0, 0}
  };
X = inverse(A) * N * A;
I = ideal(X_(3,0), X_(3,1));
assert(not isGVD(I, ShowOutput=>false))
///
-- ~0.75 seconds, might be as good as we will get for a not GVD Hessenberg patch ideal


--------------------------------------------------------------------------------
-- Test isLexGVD
--------------------------------------------------------------------------------


--TEST///
--///


--------------------------------------------------------------------------------
-- Test isUnmixed
--------------------------------------------------------------------------------


TEST///  -- Not unmixed by [SM, Example 1.6]
R = QQ[x_1..x_5];
I = ideal(x_1*x_3, x_1*x_4, x_1*x_5, x_2*x_3, x_2*x_4, x_2*x_5);
assert(not isUnmixed I)
///


TEST///  -- Unmixed by [DH]
R = QQ[x_11..x_15, x_21..x_24, x_31..x_33, x_41, x_42, x_51];
A = matrix{
  {x_11, x_12, x_13, x_14, x_15, 1},
  {x_21, x_22, x_23, x_24, 1, 0},
  {x_31, x_32, x_33, 1, 0, 0},
  {x_41, x_42, 1, 0, 0, 0},
  {x_51, 1, 0, 0, 0, 0},
  {1, 0, 0, 0, 0, 0}
  };
N = matrix{
  {0, 1, 0, 0, 0, 0},
  {0, 0, 1, 0, 0, 0},
  {0, 0, 0, 1, 0, 0},
  {0, 0, 0, 0, 1, 0},
  {0 ,0, 0, 0, 0, 1},
  {0, 0, 0, 0, 0, 0}
  };
X = inverse(A) * N * A;
I = ideal( X_(2,0), X_(3,0), X_(3,1), X_(4,0), X_(4,1), X_(4,2), X_(5,0), X_(5,1), X_(5,2), X_(5,3) );
assert(isUnmixed I)
///


--------------------------------------------------------------------------------
-- Test isWeaklyGVD
--------------------------------------------------------------------------------


TEST///  -- [KR, Example 4.10]
R = QQ[x,y,z,w,r,s];
I = ideal(y*(z*s - x^2), y*w*r, w*r*(x^2 + s^2 + z^2 + w*r));
assert(isWeaklyGVD(I, ShowOutput=>false))
///


TEST///  -- not GVD, w = (1,3,2,4), h = (3,3,4,4)
R = QQ[x_21, x_22, x_31, x_41..x_43];
A = matrix{
  {1, 0, 0, 0},
  {x_21, x_22, 1, 0},
  {x_31, 1, 0, 0},
  {x_41, x_42, x_43, 1}
  };
N = matrix{
  {0, 1, 0, 0},
  {0, 0, 1, 0},
  {0, 0, 0, 1},
  {0, 0, 0, 0}
  };
X = inverse(A) * N * A;
I = ideal(X_(3,0), X_(3,1));
assert(isWeaklyGVD(I, ShowOutput=>false))
///


--------------------------------------------------------------------------------
-- Test NyI  --** note to self: just re-use the test cases from oneStepGVD
--------------------------------------------------------------------------------


--TEST///
--///


--------------------------------------------------------------------------------
-- Test oneStepGVD
--------------------------------------------------------------------------------


TEST///  -- [KR, Example 2.16]
R = QQ[x..z,w,r,s];
I = ideal( y*(z*s - x^2), y*w*r, w*r*(z^2 + z*x + w*r + s^2) );
assert( oneStepGVD(I, y, CheckDegenerate=>true) == {true, ideal(x*z*w*r+z^2*w*r+w^2*r^2+w*r*s^2,w*r,x^2-z*s), ideal(x*z*w*r+z^2*w*r+w^2*r^2+w*r*s^2), "nondegenerate"} )
///


TEST///  -- [KR, Example 4.10]
R = QQ[x..z,w,r,s];
I = ideal( y*(z*s - x^2), y*w*r, w*r*(x^2 + s^2 + z^2 + w*r) );
assert( oneStepGVD(I, y, CheckDegenerate=>true) == {true, ideal(z*s-x^2, w*r), ideal(x^2*w*r+w*r*s^2+z^2*w*r+w^2*r^2), "nondegenerate"} )
///


end--
