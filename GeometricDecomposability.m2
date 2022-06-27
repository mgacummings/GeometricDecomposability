indetOrder-- -*- coding: utf-8 -*-

newPackage(
        "GeometricDecomposability",
        Version => "0.4",
        Date => "June 15, 2022",
        Headline => "A package to check if ideals are geometrically vertex decomposable",
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
        Keywords => {"Commutative Algebra"},
        PackageImports => {"PrimaryDecomposition", "Depth"},  -- I don't think these need to be imported for the user? As a result we use PackageImports and not PackageExports
        HomePage => ""  -- homepage for the package, if one exists, otherwise leave blank/remove
        )

        export {
        -- functions
        "CyI",
        "findLexCompatiblyGVDOrder",
        "findOneStepGVD",
        "getGVDIdeal",
        "isGeneratedByIndeterminates",
        "isGVD",
        "isLexCompatiblyGVD",
        "isUnmixed",
        "isWeaklyGVD",
        "NyI",
        "oneStepGVD",
        "yInit",

        -- options
        "CheckCM",
        "IsIdealHomogeneous",
        "IsIdealUnmixed",
        "OnlyDegenerate",
        "OnlyNondegenerate",
        "RandomSeed",
        "Verbose",
        "VerifyDegenerate"
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

findLexCompatiblyGVDOrder = method(TypicalValue => List, Options => {RandomSeed => 1})
findLexCompatiblyGVDOrder(Ideal) := opts -> I -> (
        -- restrict to the ring of indeterminates appearing in I by [CDRV, tensor product result]
        setRandomSeed opts.RandomSeed;
        possibleOrders := random permutations support I;

        for indetOrder in possibleOrders do (
                if isLexCompatiblyGVD(I, indetOrder, Verbose=>false) then return {true, indetOrder};
                );
        return {false};   -- no order worked
        )

--------------------------------------------------------------------------------

findOneStepGVD = method(TypicalValue => List, Options => {OnlyNondegenerate => false, OnlyDegenerate => false})
findOneStepGVD(Ideal) := opts -> I -> (
        -- returns a list of indeterminates for which there exists a one step geometric vertex decomposition

        if opts.OnlyNondegenerate and opts.OnlyDegenerate then (
                error("a geometric vertex decomposition cannot be both degenerate and nondegenerate");
                return;
                );

        satisfiesOneStep := (I, y, ND, D) -> (
                if ND or D then (
                        oneStep := oneStepGVD(I, y, VerifyDegenerate=>true);
                        if ND then (
                                return oneStep_0 and oneStep_3 == "nondegenerate";
                                ) else (
                                return oneStep_0 and oneStep_3 == "degenerate";
                                )
                        );
                return (oneStepGVD(I, y))_0;
                );

        R := ring I;
        indets := support I;
        L := for y in indets list (if satisfiesOneStep(I, y, opts.OnlyNondegenerate, opts.OnlyDegenerate) then y else 0);
        return delete(0, L);
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
        R := ring I;
        indeterminates := gens R;
        gensI := first entries gens I;
        return isSubset(delete(0, gensI), indeterminates);
        )

--------------------------------------------------------------------------------

-- [KR, Definition 2.7]
isGVD = method(TypicalValue => Boolean, Options => {Verbose => false, IsIdealUnmixed => false, CheckCM => "once", IsIdealHomogeneous => false})
isGVD(Ideal) := opts -> I -> (
        R := ring I;
        printIf(opts.Verbose, toString I);

        if I == 0 then (printIf(opts.Verbose, "-- zero ideal"); return true);
        if I == 1 then (printIf(opts.Verbose, "-- unit ideal"); return true);
        if (isGeneratedByIndeterminates I) then (printIf(opts.Verbose, "-- generated by indeterminates"); return true);

        if not opts.IsIdealUnmixed then (
                if not (isUnmixed I) then (printIf(opts.Verbose, "-- ideal is not unmixed"); return false);
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

                printIf(opts.Verbose, "-- decomposing with respect to " | toString y);

                (isValid, C, N) := toSequence oneStepGVD(I, y, Verbose=>opts.Verbose);
                if not isValid then continue;  -- go back to top of for loop

                printIf(opts.Verbose, "-- C = " | toString C);
                printIf(opts.Verbose, "-- N = " | toString N);

                CisGVD := isGVD(C, Verbose=>opts.Verbose, IsIdealUnmixed=>true, CheckCM=>CMTable#(opts.CheckCM), IsIdealHomogeneous=>x);
                NisGVD := isGVD(N, Verbose=>opts.Verbose, IsIdealUnmixed=>true, CheckCM=>CMTable#(opts.CheckCM), IsIdealHomogeneous=>x);

                if (CisGVD and NisGVD) then return true;
                );

        -- if we are here, no choice of y worked
        return false;
        )

--------------------------------------------------------------------------------

-- [KR, Definition 2.11]
isLexCompatiblyGVD = method(TypicalValue => Boolean, Options => {Verbose => false, IsIdealUnmixed => false, CheckCM => "once", IsIdealHomogeneous => false})
isLexCompatiblyGVD(Ideal, List) := opts -> (I, indetOrder) -> (
        R := ring I;
        printIf(opts.Verbose, toString I);

        if I == 0 then (printIf(opts.Verbose, "-- zero ideal"); return true);
        if I == 1 then (printIf(opts.Verbose, "-- unit ideal"); return true);
        if (isGeneratedByIndeterminates I) then (printIf(opts.Verbose, "-- generated by indeterminates"); return true);

        supportIndets := support I;
        trimmedOrder := select(indetOrder, i -> member(sub(i, R), supportIndets));

        if not opts.IsIdealUnmixed then (
                if not (isUnmixed I) then (printIf(opts.Verbose, "-- ideal is not unmixed"); return false);
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

        printIf(opts.Verbose, "-- decomposing with respect to " | toString y);

        (isValid, C, N) := toSequence oneStepGVD(I, y, Verbose=>opts.Verbose);
        if not isValid then return false;  -- order didn't work

        printIf(opts.Verbose, "-- C = " | toString C);
        printIf(opts.Verbose, "-- N = " | toString N);

        CisGVD := isLexCompatiblyGVD(C, remainingOrder, Verbose=>opts.Verbose, IsIdealUnmixed=>true, CheckCM=>CMTable#(opts.CheckCM), IsIdealHomogeneous=>x);
        NisGVD := isLexCompatiblyGVD(N, remainingOrder, Verbose=>opts.Verbose, IsIdealUnmixed=>true, CheckCM=>CMTable#(opts.CheckCM), IsIdealHomogeneous=>x);

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
isWeaklyGVD = method(TypicalValue => Boolean, Options => {IsIdealUnmixed => false, Verbose => false})
isWeaklyGVD(Ideal) := opts -> I -> (
        R := ring I;
        printIf(opts.Verbose, toString I);

        if I == 0 then (printIf(opts.Verbose, "-- zero ideal"); return true);
        if I == 1 then (printIf(opts.Verbose, "-- unit ideal"); return true);
        if (isGeneratedByIndeterminates I) then (printIf(opts.Verbose, "-- generated by indeterminates"); return true);

        if not opts.IsIdealUnmixed then (
                if not (isUnmixed I) then (printIf(opts.Verbose, "-- ideal is not unmixed"); return false);
                );

        -- check all options for y until one works
        for y in (support I) do (

                printIf(opts.Verbose, "-- decomposing with respect to " | toString y);

                oneStep := oneStepGVD(I, y, VerifyDegenerate=>true, Verbose=>opts.Verbose);
                isValid := oneStep_0;
                if not isValid then continue;  -- go back to top of for loop

                (C, N, degenerateOutput) := (oneStep_1, oneStep_2, oneStep_3);
                isDegenerate := (degenerateOutput == "degenerate");
                degenerateTable := new HashTable from {true => "degenerate", false => "nondegenerate"};

                printIf(opts.Verbose, "-- C = " | toString C);
                printIf(opts.Verbose, "-- N = " | toString N);
                printIf(opts.Verbose, "-- form a " | degenerateTable#isDegenerate | " geometric vertex decomposition");

                if isDegenerate then (
                        -- degenerate case
                        if isWeaklyGVD(N, IsIdealUnmixed=>true, Verbose=>opts.Verbose) then return true else continue;

                        ) else (
                        -- nondegenerate case
                        if not (radical(N, Unmixed=>true) == N and isCM(ring N/N)) then continue;
                        if isWeaklyGVD(C, IsIdealUnmixed=>true, Verbose=>opts.Verbose) then return true else continue;
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
oneStepGVD = method(TypicalValue => List, Options => {Verbose => false, VerifyDegenerate => false})
oneStepGVD(Ideal, RingElement) := opts -> (I, y) -> (

        -- set up the rings
        indeterminates := switch(0, index y, gens ring y);
        remainingIndets := drop(gens ring y, {index y, index y});
        cr := coefficientRing ring I;

        givenRing := ring I;
        lexRing := cr[indeterminates, MonomialOrder=>Lex];
        contractedRing := cr[remainingIndets];

        -- pull evertying into a lex ring
        I1 := sub(I, lexRing);
        y1 := sub(y, lexRing);
        inyForm := sub(yInit(I1, y1), lexRing);
        G := first entries gens gb I1;

        -- get N_{y,I}
        gensN := delete(0, apply(G, g -> isInN(g, y1)));
        NyI := ideal(gensN);

        -- get C_{y, I} and determine whether the GB is squarefree in y
        gensC := delete(true, flatten(apply(G, g -> isInC(g, y1))));
        squarefree := (number(gensC, i -> (i === false)) == 0);  -- squarefree is true iff number of `false` in gensC is 0
        CyI := ideal(delete(false, gensC));

        -- [KR, Lemma 2.6]
        if not squarefree then (
                printIf(opts.Verbose, "Warning: Gröbner basis not squarefree in " | toString y);
                return {false, sub(CyI, givenRing), sub(NyI, givenRing)};
                );

        -- check that the intersection holds
        -- sub CyI, NyI into lexRing in case either is zero or unit ideal
        validOneStep := ( intersect( sub(CyI, lexRing), sub(NyI, lexRing) + ideal(y1) ) == inyForm );

        C := sub(CyI, givenRing);
        N := sub(NyI, givenRing);

        if not validOneStep then (
                printIf(opts.Verbose, "Warning: not a valid geometric vertex decomposition");
                return {false, C, N};
                );

        -- check unmixedness of both CyI and NyI
        isUnmixedC := isUnmixed C;
        isUnmixedN := isUnmixed N;

        if not isUnmixedC then (
                printIf(opts.Verbose, "Warning: CyI is not unmixed");
                );
        if not isUnmixedN then (
                printIf(opts.Verbose, "Warning: NyI is not unmixed");
                );
        if not (isUnmixedC and isUnmixedN) then (
                return {false, CyI, NyI};
                );

        if opts.VerifyDegenerate then (
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

-- [KMY, Section 2.1]
yInit = method(TypicalValue => Ideal)
yInit(Ideal, RingElement) := (I, y) -> (
        givenRing := ring I;

        -- set up the ring
        indeterminates := switch(0, index y, gens ring y);
        cr := coefficientRing ring I;

        initYFormRing := cr[indeterminates, MonomialOrder=>ProductOrder{1, #indeterminates - 1}];

        -- get the ideal of initial y-forms using the product order
        I = sub(I, initYFormRing);
        y = sub(y, initYFormRing);
        inyFormIdeal := ideal leadTerm(1,I);

        return sub(inyFormIdeal, givenRing);
        )

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

--** METHODS (HIDDEN FROM USER)

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
        if degree(y, f) == 0 then return f else return 0;  -- 0 is a temp value which we remove immediately
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
                        a package to check whether ideals are geometrically vertex decomposable

                Description
                        Text

                                This package includes routines to check whether an ideal is
                                geometrically vertex decomposable. The notion of geometric vertex
                                decomposability can be considered as a generalization of the properties
                                of the Stanley-Reisner ideal of a vertex decomposable simplicial complex.
                                Geometrically vertex decomposable ideals are based upon the geometric vertex
				decomposition defined by Knutson, Miller, and Yong [KMY].  Using geometric
				vertex decomposition, Klein and Rajchgot gave a recursive definition for
				geometrically vertex decomposable ideals in [KR].

                                An unmixed ideal $I$ in a polynomial ring $R$ is geometrically vertex
                                decomposable if it is the zero ideal, the unit ideal, an ideal generated
                                by indeterminates, or if there is a indeterminate $y$ of $R$ such the
                                two ideals $C_{y,I}$ and $N_{y,I}$ that are constructed from $I$ are
                                both geometrically vertex decomposable. For the complete definition, see
                                @TO isGVD@.

                                Observe that a geometrically vertex decomposable ideal is recursively
                                defined. The complexity of verifying that an ideal is geometrically
                                vertex decomposable will increase as the number of indeterminates
                                appearing in the ideal increases.

                Acknowledgement
                        We thank S. Da Silva, J. Rajchgot, and M. Harada for feedback. Cummings
                        was partially supported by an NSERC USRA. Van Tuyl's research is partially
                        supported by NSERC Discovery Grant 2019-05412.

                References

                        [CDSRVT] M. Cummings, S. Da Silva, J. Rajchgot, and A. Van Tuyl.
                        Geometric Vertex Decomposition and Liaison for Toric Ideals of
                        Graphs. In Preparation (2022).

                        [DSH] S. Da Silva and M. Harada. Regular Nilpotent Hessenberg Varieties,
                        Gröbner Bases, and Toric Degenerations. In preparation (2022).

                        [KMY] A. Knutson, E. Miller, and A. Yong. Gröbner Geometry of Vertex
                        Decompositions and of Flagged Tableaux. J. Reine Angew. Math. 630 (2009)
                        1–31.

                        [KR] P. Klein and J. Rajchgot. Geometric Vertex Decomposition and
                        Liaison. Forum of Math, Sigma, 9 (2021) e70:1-23.

                        [SM] H. Saremi and A. Mafi. Unmixedness and Arithmetic Properties of
                        Matroidal Ideals. Arch. Math. 114 (2020) 299–304.

                Subnodes
                        CheckCM
                        CyI
                        findLexCompatiblyGVDOrder
                        findOneStepGVD
                        getGVDIdeal
                        isGeneratedByIndeterminates
                        isGVD
                        IsIdealHomogeneous
                        IsIdealUnmixed
                        isLexCompatiblyGVD
                        isUnmixed
                        isWeaklyGVD
                        NyI
                        oneStepGVD
                        OnlyDegenerate
                        OnlyNondegenerate
                        RandomSeed
                        Verbose
                        VerifyDegenerate
                        yInit
///

--******************************************************************************
-- Documentation for functions
--******************************************************************************


doc///
        Node
                Key
                        CyI
                        (CyI, Ideal, RingElement)
                Headline
                        computes the ideal $C_{y,I}$ for a given ideal and indeterminate
                Usage
                        CyI(I, y)
                Inputs
                        I:Ideal
                        y:RingElement
                                an indeterminate in the ring
                Outputs
                        J:Ideal

                Caveat
                        This method is a shortcut to extract the ideal $C_{y,I}$ as computed
                        in @TO oneStepGVD@. That is, to compute $C_{y,I}$, we call {\tt oneStepGVD}.
                        As a result, work is also done in the background to compute $N_{y,I}$ at
                        the same time, and as such, the user is encouraged to call {\tt oneStepGVD}
                        directly if they want both the $C_{y,I}$ and $N_{y,I}$ ideals to avoid
                        performing the same computation twice.

	        Description
	                Text
			        Let $y$ be a variable of the polynomial ring $R = k[x_1,\ldots,x_n]$. A monomial ordering $<$ on $R$ is said to be
                                {\it $y$-compatible} if the initial term of $f$ satisfies ${\rm in}_<(f) = {\rm in}_<({\rm in}_y(f))$ for all $f \in R$.  Here,
				${\rm in}_y(f)$ is the {\it initial $y$-form} of $f$, the non-zero coefficient of the highest power of $y^i$ appearing in $f$.

                                Given an ideal $I$ and a $y$-compatible monomial ordering $<$, let $G(I) = \{ g_1,\ldots,g_m\}$ be a Gröbner basis of $I$ with respect to this
                                ordering.  For $i=1,\ldots,m$, write $g_i$ as $g_i = y^{d_i}q_i + r_i$, where $y$ does not divide any term of $q_i$;
                                that is, ${\rm in}_y(g_i) = y^{d_i}q_i$.   Given this setup, the ideal $C_{y,I}$ is given by
                                $$C_{y,I} = \langle q_1,\ldots,q_m\rangle$$
			        This functions  takes an ideal $I$ and variable $y$, and returns $C_{y,I}$

                                The ideal $C_{y,I}$ does not depend upon the choice of the Gröbner basis or
                        	a particular $y$-compatible order (see comment after Defintion 2.3 of [KR]).
				When computing $C_{y,I}$ we use a lexicographical ordering
                        	on $R$ where $y > x_j$ for all $i \neq j$ if $y = x_i$ since this gives us a $y$-compatible order.

                                The ideal $I$ in the example below is the edge ideal of the complete graph $K_4$.
                        Example
                                R = QQ[a,b,c,d];
                                I = ideal(a*b,a*c,a*d,b*c,b*d,c*d); -- edge ideal of a complete graph K_4, a chordal graph
                                CyI(I,b)
				L = oneStepGVD(I,b);
			        L_1 == CyI(I,b) -- CyI is the second element in the list given oneStepGVD
    	    	References
		        [KR] P. Klein and J. Rajchgot. Geometric Vertex Decomposition and
                        Liaison. Forum of Math, Sigma, 9 (2021) e70:1-23.
                SeeAlso
                        getGVDIdeal
                        NyI
                        oneStepGVD
///


doc///
        Node
                Key
                        findLexCompatiblyGVDOrder
                        (findLexCompatiblyGVDOrder, Ideal)
                Headline
                        finds a lexicographic monomial order $<$ such that the ideal is $<$-compatibly geometrically vertex decomposable
                Usage
                        findLexCompatiblyGVDOrder I
                        findLexCompatiblyGVDOrder(I, RandomSeed=>seed)
                Inputs
                        I:Ideal
                        seed:ZZ
                Outputs
                        L:List
                                if no order exists, returns {\tt \{false\}}, otherwise returns {\tt \{true, L\}},
                                where {\tt L} is the lex order which works, stored as a list

                Description

                        Text

                                An ideal is $<$-compatibly geometrically vertex decomposable if
                                there exists a (lexicographic) order $<$ such that at each one-step
                                geometric vertex decomposition, we pick $y$ to be the most expensive
                                indeterminate remaining in the ideal [KR, Definition 2.11].

                                This method computes all possible lex orders on the indeterminates
                                appearing in the ideal and checks each until one which works is
                                found.

                                Once the list of orders is computed, the list is shuffled. For
                                a consistent order in the computation, set a @TO RandomSeed@.

			Example
			        R = QQ[x,y];
                                I = ideal(x^2 - y^2);
				findLexCompatiblyGVDOrder I
                                R = QQ[x,y,z];
                                I = ideal(x-y, x-z);
                                findLexCompatiblyGVDOrder I

                Caveat
                        The program does not learn from orders that do not work. For instance,
                        suppose that there does not exist a geometric vertex decomposition for
                        a given ideal with respect to some $y$. This program will nonetheless
                        check all the lex orders with $y$ as the most expensive indeterminate
                        in the order. As a result, the execution time may be very slow.

                        It is for this reason that the monomial orders are shuffled upon their
                        generation. That is, if we did not shuffle the orders and $y$ was
                        the first choice for the most expensive indeterminate with respect
                        to $<$, then if there are $n-1$ other indeterminates, we would check
                        $(n-1)!$ monomial orders, all beginning with $y$, that do not work before
                        trying another choice of most expensive indeterminate.

		References
		        [KR] P. Klein and J. Rajchgot. Geometric Vertex Decomposition and
                        Liaison. Forum of Math, Sigma, 9 (2021) e70:1-23.

                SeeAlso
                        isLexCompatiblyGVD
///


doc///
        Node
                Key
                        findOneStepGVD
                        (findOneStepGVD, Ideal)
                Headline
                        for which indeterminates does there exist a geometric vertex decomposition
                Usage
                        findOneStepGVD I
                        findOneStepGVD(I, OnlyNondegenerate=>nondegenerate)
                        findOneStepGVD(I, OnlyDegenerate=>degenerate)
                Inputs
                        I:Ideal
                        nondegenerate:Boolean
                        degenerate:Boolean
                Outputs
                        L:List

                Description
                        Text
                                Returns a list containing the $y$ for which there exists a @TO oneStepGVD@.
                                All indeterminates $y$ which appear in the ideal are checked.

                        Example
                                R = QQ[x,y,z]
                                I = ideal(x-y, x-z)
                                findOneStepGVD I

                        Text
                                The following example is [KR, Example 2.16].

                        Example
                                R = QQ[x,y,z,w,r,s]
                                I = ideal(y*(z*s - x^2), y*w*r, w*r*(z^2+z*x+w*r+s^2))
                                findOneStepGVD I

                References
		        [KR] P. Klein and J. Rajchgot. Geometric Vertex Decomposition and
                        Liaison. Forum of Math, Sigma, 9 (2021) e70:1-23.

                SeeAlso
                        oneStepGVD
///


doc///
        Node
                Key
                        getGVDIdeal
                        (getGVDIdeal, Ideal, List)
                Headline
                        computes the $C_{y,I}$ or $N_{y,I}$ ideal at any point in the GVD recursion tree
                Usage
                        getGVDIdeal(I, L)
                Inputs
                        I:Ideal
                        L:List
                                a nested list where each list within {\tt L} is of length two, the
                                first entry is either "C" or "N" and the second entry is an
                                indeterminate in the ring
                Outputs
                        M:List
                Description
                        Text
                                The purpose of {\tt getGVDIdeal} is to return the ideal generated
                                by a sequence of choices of $C$ or $N$ ideals and corresponding
                                choices of indeterminates $y$.

				Given an ideal $I$ and variable $y_1$ in $R = k[x_1,\ldots,x_n]$, we can compute the ideals
				$C_{y_1,I}$ and $N_{y_1,I}$ (see @TO isGVD@ for the definition of these ideals).  But
				then for each of these ideals in the ring $R = k[x_1,\ldots,\hat{y_1},\ldots,x_n]$, we can
				then pick a new variable $y_2$ to form the ideals $C_{y_2,C_{y_1,I}}$, $C_{y_2,N_{y_1,I}}$,
				$N_{y_2,C_{y_1,I}}$ or $N_{y_2,N_{y_1,I}}$.  This process can be continued by now picking a new
				variable $y_3$, and find either the $C$ or $N$ ideals of these ideals.

				The input syntax is best explained via example. The following is
                                [KR, Example 2.16]. We are given the ideal $I$.  The input
				tells us to first find $C_{y,I}$ of $I$.  Then we find $N_{s,C_{y,I}}$.

                        Example
                                R = QQ[x,y,z,w,r,s]
                                I = ideal(y*(z*s - x^2), y*w*r, w*r*(z^2+z*x+w*r+s^2))
                                getGVDIdeal(I, {{"C", y}, {"N", s}})
                References
		        [KR] P. Klein and J. Rajchgot. Geometric Vertex Decomposition and
                        Liaison. Forum of Math, Sigma, 9 (2021) e70:1-23.

                SeeAlso
                        CyI
                        NyI
                        oneStepGVD
///


doc///
        Node
                Key
                        isGeneratedByIndeterminates
                        (isGeneratedByIndeterminates, Ideal)
                Headline
                        checks whether the ideal is generated by indeterminates
                Usage
                        isGeneratedByIndeterminates I
                Inputs
                        I:Ideal
                Outputs
                        B:Boolean
                Description
                        Text
                                An ideal is generated by indeterminates if the generators are a
                                (possibly empty) subset of the indeterminates in the ring.

				This function is used to check if a given ideal satisfies one of the conditions
				of being geometrically vertex decomposable (see @TO isGVD@).

                        Example
                                R = QQ[x,y]
                                isGeneratedByIndeterminates ideal 0
                                isGeneratedByIndeterminates ideal 1
                                isGeneratedByIndeterminates ideal(x,y)
                                isGeneratedByIndeterminates ideal(x*y)

                SeeAlso
                        isGVD
                        isLexCompatiblyGVD
                        isWeaklyGVD
///


doc///
        Node
                Key
                        isGVD
                        (isGVD, Ideal)
                Headline
                        checks whether an ideal is geometrically vertex decomposable
                Usage
                        isGVD I
                        isGVD(I, CheckCM=>cm)
                        isGVD(I, IsIdealHomogeneous=>homogeneous)
                        isGVD(I, IsIdealUnmixed=>unmixed)
                        isGVD(I, Verbose=>output)
                Inputs
                        I:Ideal
                        cm:String
                        homogeneous:Boolean
                        unmixed:Boolean
                        output:Boolean
                Outputs
                        B:Boolean
                Description
                        Text
                                This function tests if a given ideal is geometric vertex decomposable.  
		                Geometrically vertex decomposable ideals are based upon the geometric vertex
				decomposition defined by Knutson, Miller, and Yong [KMY].  Using geometric
				vertex decomposition, Klein and Rajchgot gave a recursive definition for
				geometrically vertex decomposable ideals in [KR, Definition 2.7].  This definition generalizes the properties
				of a square-free monomial ideal whose associated simplicial complex is vertex decomposable.

                                We include the definition here.  Let $y$ be a variable of the polynomial ring $R = k[x_1,\ldots,x_n]$.
				A monomial ordering $<$ on $R$ is said to be {\it $y$-compatible} if the initial term of $f$ satisfies ${\rm in}_<(f) = {\rm in}_<({\rm in}_y(f))$ for all $f \in R$.  Here,
				${\rm in}_y(f)$ is the {\it initial $y$-form} of $f$, the non-zero coefficient of the highest power of $y^i$ appearing in $f$.
				We set ${\rm in}_y(I) = \langle {\rm in}_y(f) ~|~ f \in I \rangle$ to be the ideal generated by all the initial $y$-forms in $I$.
				
                                Given an ideal $I$ and a $y$-compatible monomial ordering $<$, let $G(I) = \{ g_1,\ldots,g_m\}$ be a Gröbner basis of $I$ with respect to this
                                ordering.  For $i=1,\ldots,m$, write $g_i$ as $g_i = y^{d_i}q_i + r_i$, where $y$ does not divide any term of $q_i$;
                                that is, ${\rm in}_y(g_i) = y^{d_i}q_i$.   Given this setup, we define two ideals:
                                $$C_{y,I} = \langle q_1,\ldots,q_m\rangle$$
                                and
                                $$N_{y,I} = \langle q_i ~|~ d_i = 0 \rangle.$$
                                Recall that an ideal $I$ is {\it unmixed} if the ideal $I$  satisfies $\dim(R/I) = \dim(R/P)$ for all associated primes $P \in {\rm Ass}_R(R/I)$.

                                An ideal $I$ of $R =k[x_1,\ldots,x_n]$ is {\it geometrically vertex decomposable} if $I$ is unmixed and

                                (1)  $I = \langle 1 \rangle$, or $I$ is generated by a (possibly empty) subset of variables of $R$, or

                                (2) there is a variable $y = x_i$ in $R$ and a $y$-compatible monomial ordering $<$ such that
                                        $${\rm in}_y(I) = C_{y,I} \cap (N_{y,I} + \langle y \rangle),$$
                                        and the contractions of the
                                        ideals $C_{y,I}$ and $N_{y,I}$ to the ring
                                        $k[x_1,\ldots,x_{i-1},x_{i+1},\ldots,x_n]$ are geometrically
                                        vertex decomposable.

                        	{\it NOTE:}  The ideals $C_{y,I}$ and $N_{y,I}$ do not depend upon the choice of the Gröbner basis or
                        	a particular $y$-compatible order (see comment after [KR, Defintion 2.3]).
                        	When computing $C_{y,I}$ and $N_{y,I}$ we use a lexicographical ordering
                        	on $R$ where $y > x_j$ for all $i \neq j$ if $y = x_i$ since this gives us a $y$-compatible order.

                        Example
                	        R = QQ[a,b,c,d]
                		f = 3*a*b + 4*b*c+ 16*a*c+18*d
                		i = ideal(f)
                		isGVD(i)

                        Text
                	        Square-free monomial ideals that are geometrically vertex decomposable are precisely those square-free monomial ideals
                		whose associated simplicial complex are vertex decomposable [KR, Proposition 2.9].
				 The edge ideal of a chordal graph corresponds to a simplicial
                		complex that is vertex decomposable.  The option {\tt Verbose} shows the intermediate steps; in particular, {\tt Verbose}
				displays what variable is being used to test a decomposition, as well as the ideals
				$C_{y,I}$ and $N_{y,I}$.
                        Example
                                R = QQ[a,b,c,d]
                                i = ideal(a*b,a*c,a*d,b*c,b*d,c*d) -- edge ideal of a complete graph K_4, a chordal graph
                                isGVD(i,Verbose=>true)

                        Text
                                The following example gives an example of toric ideal of graph that is geometrically vertex decomposable, and another example
                		of a toric ideal that is not geometric vertex decomposable.  The second toric ideal is not Cohen-Macaulay, so it
                		cannot be geometrically vertex decomposable.

                        Example
                	        R = QQ[e_1..e_7]
                		i = ideal(e_2*e_7-e_5*e_6,e_1*e_4-e_2*e_3) -- the toric ideal of a graph
                		isGVD i
                	        R = QQ[e_1..e_10]
                		i = ideal(e_1*e_4-e_2*e_3,e_2^2*e_7*e_8*e_9-e_4^2*e_5*e_6*e_10,e_1*e_2*e_7*e_8*e_9-e_3*e_4*e_5*e_6*e_10,e_1^2*e_7*e_8*e_9-e_3^2*e_5*e_6*e_10)
                		isGVD i
		References
		        [KR] P. Klein and J. Rajchgot. Geometric Vertex Decomposition and
                        Liaison. Forum of Math, Sigma, 9 (2021) e70:1-23.

                SeeAlso
                        CheckCM
                        isGeneratedByIndeterminates
                        IsIdealHomogeneous
                        IsIdealUnmixed
                        isLexCompatiblyGVD
                        isUnmixed
                        isWeaklyGVD
                        oneStepGVD
                        Verbose
///


doc///
        Node
                Key
                        isLexCompatiblyGVD
                        (isLexCompatiblyGVD, Ideal, List)
                Headline
                        checks whether an ideal is <-compatibly geometrically vertex decomposable for a given order
                Usage
                        isLexCompatiblyGVD(I, L)
                        isLexCompatiblyGVD(I, L, CheckCM=>cm)
                        isLexCompatiblyGVD(I, L, IsIdealHomogeneous=>homogeneous)
                        isLexCompatiblyGVD(I, L, IsIdealUnmixed=>unmixed)
                        isLexCompatiblyGVD(I, L, Verbose=>output)
                Inputs
                        I:Ideal
                        L:List
                        cm:String
                        homogeneous:Boolean
                        unmixed:Boolean
                        output:Boolean
                Outputs
                        B:Boolean
                Description
		 	Text
			        An ideal is $<$-compatibly geometrically vertex decomposable if
                                there exists a (lexicographic) order $<$ such that at each one-step
                                geometric vertex decomposition, we pick $y$ to be the most expensive
                                indeterminate remaining in the ideal [KR, Definition 2.11].

                                This method returns a Boolean value depending upon whether or not
				the given ideal is $<$-comptabibly geometrically vertex decomposable with
				respect to a given ordering lex ordering of the vertices.

				Compare this function to the command @TO findLexCompatiblyGVDOrder@ which checks all possible lex
				orders of the variables in order to find at least one $<$-comptabibly lex order.

				Below is [KR, Example 2.16], which is an example of an ideal that is not $<$-compatibly geometrically
				vertex decomposable.   Any permutation of the variables we give in this example will result in {\tt false}.
			Example
			        R = QQ[x..z,w,r,s];
                                I = ideal( y*(z*s - x^2), y*w*r, w*r*(z^2 + z*x + w*r + s^2));
				isLexCompatiblyGVD(I,{x,y,z,w,r,s})
				isLexCompatiblyGVD(I,{s,x,w,y,r,z},Verbose=>true)
                References
		        [KR] P. Klein and J. Rajchgot. Geometric Vertex Decomposition and
                        Liaison. Forum of Math, Sigma, 9 (2021) e70:1-23.


                SeeAlso
                        CheckCM
                        isGeneratedByIndeterminates
                        isGVD
                        IsIdealHomogeneous
                        IsIdealUnmixed
                        isUnmixed
                        isWeaklyGVD
                        oneStepGVD
                        Verbose
///


doc///
        Node
                Key
                        isUnmixed
                        (isUnmixed, Ideal)
                Headline
                        checks whether an ideal is unmixed
                Usage
                        isUnmixed I
                Inputs
                        I:Ideal
                Outputs
                        B:Boolean
                Description
		        Text
			        A function that checks if an ideal $I$ is unmixed, i.e., all of the associated primes of $I$ have the same height.

			        The function is used by @TO isGVD@ to check if the ideal $I$ satisfies one the requirements to be a geometrically
			        vertex decomposable ideal.

			        The following example uses  [SM, Example 1.6]
		        Example
			        R = QQ[x_1..x_5];
                                I = ideal(x_1*x_3, x_1*x_4, x_1*x_5, x_2*x_3, x_2*x_4, x_2*x_5);
				isUnmixed I
		References
		        [SM] H. Saremi and A. Mafi. Unmixedness and Arithmetic Properties of
                        Matroidal Ideals. Arch. Math. 114 (2020) 299-304.
                SeeAlso
                        isGVD
                        isLexCompatiblyGVD
                        isWeaklyGVD
///


doc///
        Node
                Key
                        isWeaklyGVD
                        (isWeaklyGVD, Ideal)
                Headline
                        checks whether an ideal is weakly geometrically vertex decomposable
                Usage
                        isWeaklyGVD I
                        isWeaklyGVD(I, IsIdealUnmixed=>unmixed)
                        isWeaklyGVD(I, Verbose=>output)
                Inputs
                        I:Ideal
                        unmixed:Boolean
                        output:Boolean
                Outputs
                        B:Boolean
                Description
		        Text
			        This function tests if a given ideal is weakly geometrically vertex decomposable, as defined in [KR, Definition 4.6].

				See @TO isGVD@ for the definition of the ideals $C_{y,I}$ and $N_{y,I}$ used below.  Furthermore, we say that a geometric
				vertex decomposition is {\it degenerate} if $C_{y,I} = \langle 1 \rangle$ or if $\sqrt{C_{y,I}} = \sqrt{N_{y,I}}$.

				An ideal is {\it weakly geometrically vertex decomposable} if $I$ is unmixed and

                                (1) $I = \langle 1 \rangle$, or $I$ is generated by a (possibly empty) subset of variables of $R$, or

				(2) (Degenerate Case) for some variable $y = x_j$ of $R$, ${\rm in}_y(I) = C_{y,I} \cap (N_{y,I} + \langle y \rangle)$ is
				a degenerate geometric vertex decomposition and the the contraction of $N_{y,I}$ to the ring $k[x_1,\ldots,\hat{y},\ldots,x_n]$
				is weakly geometrically vertex decomposable, or

				(3) (Nondegenerate Case) for some variable $y= x_j$ of $R$,  ${\rm in}_y(I) = C_{y,I} \cap (N_{y,I} + \langle y \rangle)$ is
				a non-degenerate geometric vertex decomposition, the contraction $C_{y,I}$ to the ring  $k[x_1,\ldots,\hat{y},\ldots,x_n]$
				is weakly geometrically vertex decomposable, and $N_{y,I}$ is radical and Cohen-Macaulay.

		                The following example is based upon [KR, Example 4.10]; this is an example of an ideal that is weakly geometrically
				vertex decomposable, but not geometrically vertex decomposable.
		        Example
                	        R = QQ[x..z,w,r,s];
                                I = ideal( y*(z*s - x^2), y*w*r, w*r*(x^2 + s^2 + z^2 + w*r));
				isWeaklyGVD I
				isGVD I

               References
		        [KR] P. Klein and J. Rajchgot. Geometric Vertex Decomposition and
                        Liaison. Forum of Math, Sigma, 9 (2021) e70:1-23.

               SeeAlso
                        isGeneratedByIndeterminates
                        isGVD
                        IsIdealUnmixed
                        isLexCompatiblyGVD
                        isUnmixed
                        oneStepGVD
                        Verbose
///


doc///
        Node
                Key
                        NyI
                        (NyI, Ideal, RingElement)
                Headline
                        computes the ideal $N_{y,I}$ for a given ideal and indeterminate
                Usage
                        NyI(I, y)
                Inputs
                        I:Ideal
                        y:RingElement
                                an indeterminate in the ring
                Outputs
                        J:Ideal

                Caveat
                        This method is a shortcut to extract the ideal $N_{y,I}$ as computed
                        in @TO oneStepGVD@. That is, to compute $N_{y,I}$, we call {\tt oneStepGVD}.
                        As a result, work is also done in the background to compute $C_{y,I}$ at
                        the same time, and as such, the user is encouraged to call {\tt oneStepGVD}
                        directly if they want both the $C_{y,I}$ and $N_{y,I}$ ideals to avoid
                        performing the same computation twice.
                Description
                        Text
                                Let $y$ be a variable of the polynomial ring $R = k[x_1,\ldots,x_n]$. A monomial ordering $<$ on $R$ is said to be
                                {\it $y$-compatible} if the initial term of $f$ satisfies ${\rm in}_<(f) = {\rm in}_<({\rm in}_y(f))$ for all $f \in R$.  Here,
				${\rm in}_y(f)$ is the {\it initial $y$-form} of $f$, the non-zero coefficient of the highest power of $y^i$ appearing in $f$.

                                Given an ideal $I$ and a $y$-compatible monomial ordering $<$, let $G(I) = \{ g_1,\ldots,g_m\}$ be a Gröbner basis of $I$ with respect to this
                                ordering.  For $i=1,\ldots,m$, write $g_i$ as $g_i = y^{d_i}q_i + r_i$, where $y$ does not divide any term of $q_i$;
                                that is, ${\rm in}_y(g_i) = y^{d_i}q_i$.   Given this setup, the ideal $N_{y,I}$ is given by
                                $$N_{y,I} = \langle q_i ~|~ d_i = 0\rangle$$
                                This functions  takes an ideal $I$ and variable $y$, and returns $N_{y,I}$

                                The ideal $N_{y,I}$ does not depend upon the choice of the Gröbner basis or
                        	a particular $y$-compatible order (see comment after Defintion 2.3 of [KR]).
				When computing $N_{y,I}$ we use a lexicographical ordering
                        	on $R$ where $y > x_j$ for all $i \neq j$ if $y = x_i$ since this gives us a $y$-compatible order.

                                The ideal $I$ in the example below is the edge ideal of the complete graph $K_4$.

                        Example
                                R = QQ[a,b,c,d];
                                I = ideal(a*b,a*c,a*d,b*c,b*d,c*d); -- edge ideal of a complete graph K_4, a chordal graph
                                NyI(I,b)
                                L = oneStepGVD(I,b);
                                L_2 == NyI(I,b) -- NyI is the second element in the list given by oneStepGVD
		References
		        [KR] P. Klein and J. Rajchgot. Geometric Vertex Decomposition and
                        Liaison. Forum of Math, Sigma, 9 (2021) e70:1-23.

		SeeAlso
                        CyI
                        getGVDIdeal
                        oneStepGVD
///


doc///
       Node
                Key
                        oneStepGVD
                        (oneStepGVD, Ideal, RingElement)
                Headline
                        computes a geometric vertex decomposition
                Usage
                        oneStepGVD(I, y)
                        oneStepGVD(I, y, Verbose=>output)
                        oneStepGVD(I, y, VerifyDegenerate=>degenerate)
                Inputs
                        I:Ideal
                        y:RingElement
                                an indeterminate in the ring
                        degenerate:Boolean
                        output:Boolean
                Outputs
                        L:List
                                a list containing whether the $C_{y,I}$ and $N_{y,I}$ ideals form
                                a valid geometric vertex decomposition, these ideals, and if
                                {\tt VerifyDegenerate=>true}, whether the one-step decomposition
                                is degenerate or nondegenerate
		Description
			 Text
                                This function computes a geometric vertex decomposition of an ideal based upon work of Knutson,
				Miller, and Yong [KMY, Theorem 2.1].  Geometic vertex decomposition is the key step in the recursive
			        defintion of geometically vertex decomposable ideals.  The function {\tt oneStepGVD} is repeatedly used by @TO isGVD@ to determine
				if an ideal is a geometically vertex decomposable ideal.

				Let $y$ be a variable of the polynomial ring $R = k[x_1,\ldots,x_n]$. A monomial ordering $<$ on $R$ is said to be
                                {\it $y$-compatible} if the initial term of $f$ satisfies ${\rm in}_<(f) = {\rm in}_<({\rm in}_y(f))$ for all $f \in R$.  Here,
				${\rm in}_y(f)$ is the {\it initial $y$-form} of $f$, the non-zero coefficient of the highest power of $y^i$ appearing in $f$.

                                Given an ideal $I$ and a $y$-compatible monomial ordering $<$, let $G(I) = \{ g_1,\ldots,g_m\}$ be a Gröbner basis of $I$ with respect to this
                                ordering.  For $i=1,\ldots,m$, write $g_i$ as $g_i = y^{d_i}q_i + r_i$, where $y$ does not divide any term of $q_i$;
                                that is, ${\rm in}_y(g_i) = y^{d_i}q_i$.   Given this setup, we define two ideals:
                                $$C_{y,I} = \langle q_1,\ldots,q_m\rangle$$
                                and
                                $$N_{y,I} = \langle q_i ~|~ d_i = 0 \rangle.$$

                                If ${\rm in}_y(I) = C_{y,I} \cap (N_{y,I} + \langle y \rangle),$
                                then we call this decomposition a {\it geometric vertex decomposition of $I$}.

				For a given variable $y$, the function {\tt oneStepGVD} returns a list, where the first element in the list is true or false
				depending if the given variable gives a geometric vertex decomposition of $I$, while the second element is the
				ideal $C_{y,I}$ and the third element in the list is the ideal $N_{y,I}$.

				{\it NOTE:}  The ideals $C_{y,I}$ and $N_{y,I}$ do not depend upon the choice of the Gröbner basis or
                        	a particular $y$-compatible order (see comment after Defintion 2.3 of [KR]).
                        	When computing $C_{y,I}$ and $N_{y,I}$ we use a lexicographical ordering
                        	on $R$ where $y > x_j$ for all $i \neq j$ if $y = x_i$ since this gives us a $y$-compatible order.
			Example
			        R = QQ[a,b,c,d]
                		f = 3*a*b + 4*b*c+ 16*a*c+18*d
                		i = ideal(f)
                		oneStepGVD(i,a)

                        Text
                                In the example below, the ideal $I$ is the edge ideal of the complete graph $K_4$.  We also check
				if the decomposition is degenerate (see @TO VerifyDegenerate@).
                        Example
                                R = QQ[a,b,c,d];
                                i = ideal(a*b,a*c,a*d,b*c,b*d,c*d); -- edge ideal of complete graph K_4, a chordal graph
                                oneStepGVD(i,c,VerifyDegenerate=>true)
			Text
			        The example below is the toric ideal of a graph such that the quotient ring is not Cohen-Macaulay.  By [KR, Lemma 2.6] for an ideal $I$
				to have a geometric vertex decomposition with respect to the variable $y$, no term of
				the Gröbner bases can be divided by $y^2$.  In this example, the Gröbner basis of $I$ contains an element with a term
				divisible by $e_1^2$.  So $I$ should have no geometric vertex decomposition with respect to $y = e_1$, as verified by
				the function.
			Example
                	        R = QQ[e_1..e_10];
                		i = ideal(e_1*e_4-e_2*e_3,e_2^2*e_7*e_8*e_9-e_4^2*e_5*e_6*e_10,e_1*e_2*e_7*e_8*e_9-e_3*e_4*e_5*e_6*e_10,e_1^2*e_7*e_8*e_9-e_3^2*e_5*e_6*e_10);
                		mingens gb i
				oneStepGVD(i,e_1)
		References
                        [KMY] A. Knutson, E. Miller, and A. Yong. Gröbner Geometry of Vertex
                        Decompositions and of Flagged Tableaux. J. Reine Angew. Math. 630 (2009)
                        1–31.

                        [KR] P. Klein and J. Rajchgot. Geometric Vertex Decomposition and
                        Liaison. Forum of Math, Sigma, 9 (2021) e70:1-23.
		SeeAlso
                        CyI
                        getGVDIdeal
                        isGVD
                        isLexCompatiblyGVD
                        isWeaklyGVD
                        NyI
                        Verbose
                        VerifyDegenerate
///


doc///
       Node
                Key
                        yInit
                        (yInit, Ideal, RingElement)
                Headline
                        computes the ideal of initial y-forms
                Usage
                        yInit(I, y)
                Inputs
                        I:Ideal
                        y:RingElement
                                an indeterminate in the ring
                Outputs
                        J:Ideal

		Description
			 Text
                                Let $y$ be a variable of the polynomial ring $R = k[x_1, \ldots, x_n]$. The {\it initial $y$-form} of a polynomial $f \in R$,
                                denoted ${\rm in}_y(f)$, is the sum of all terms of $f$ with the highest power of $y$. For an ideal $I \subseteq R$, let
                                ${\rm in}_y(I) = \langle {\rm in}_y(f) \mid f \in I \rangle $ be the ideal generated by the initial $y$-forms of elements of $I$.
                                This routine computes the ideal of initial $y$-forms ${\rm in}_y(I)$.

                                For more on the definition of initial $y$-forms or their corresponding ideals, see [KMY, Section 2.1]. The following example is
                                [KR, Example 2.16].

                        Example
                                R = QQ[x..z,w,r,s]
                                I = ideal( y*(z*s - x^2), y*w*r, w*r*(z^2 + z*x + w*r + s^2) )
                                yInit(I, y)


		References
                        [KMY] A. Knutson, E. Miller, and A. Yong. Gröbner Geometry of Vertex
                        Decompositions and of Flagged Tableaux. J. Reine Angew. Math. 630 (2009)
                        1–31.

                        [KR] P. Klein and J. Rajchgot. Geometric Vertex Decomposition and
                        Liaison. Forum of Math, Sigma, 9 (2021) e70:1-23.
		SeeAlso
                        oneStepGVD
///


--******************************************************************************
-- Documentation for optional inputs
--******************************************************************************


doc///
        Node
                Key
                        CheckCM
                        [isGVD, CheckCM]
                        [isLexCompatiblyGVD, CheckCM]
                Headline
                        optional argument for GVD methods
                Description
                        Text
                                Whether to check that the ideal is GVD using the result of
                                [KR, Corollary 4.5] "once" (default, only for the ideal given
                                in the input and none of the following C, N ideals), "always",
                                or "never".
                SeeAlso
                        isGVD
                        isLexCompatiblyGVD
///


doc///
        Node
                Key
                        VerifyDegenerate
                        [oneStepGVD, VerifyDegenerate]
                Headline
                        optional argument for {\tt oneStepGVD}
                Description
                        Text
                                A geometric vertex decomposition is degenerate if
                                $\sqrt{C_{y,I}} = \sqrt{N_{y,I}}$ or if $C_{y,I} = \langle 1 \rangle$,
                                and nondegenerate otherwise [KR, Section 2.2].

                                If {\tt VerifyDegenerate => true}, then {\tt oneStepGVD} returns
                                a list of length four, where the fourth entry is either
                                {\tt "degenerate"} or {\tt "nondegenerate"}.
                                Otherwise, {\tt oneStepGVD} does not check whether the geometric
                                vertex decomposition was degenerate.

                                Note that a degenerate geometric vertex decomposition does not matter
                                with regards to whether an ideal is geometrically vertex decomposable.
                                As a result, {\tt isGVD} does not check this. However, the definition
                                of weakly geometrically vertex decomposable depends on whether each
                                one-step geometric vertex decomposition is degenerate, so
                                {\tt isWeaklyGVD} asks for this check.
                SeeAlso
                        isWeaklyGVD
                        oneStepGVD
///


doc///
        Node
                Key
                        IsIdealHomogeneous
                        [isGVD, IsIdealHomogeneous]
                        [isLexCompatiblyGVD, IsIdealHomogeneous]
                Headline
                        optional argument for GVD methods
                Description
                        Text
                                Whether the input ideal is homogeneous, if known. This only matters if
                                the Cohen-Macaulay check is completed.
                SeeAlso
                        isGVD
                        isLexCompatiblyGVD
///


doc///
        Node
                Key
                        IsIdealUnmixed
                        [isGVD, IsIdealUnmixed]
                        [isLexCompatiblyGVD, IsIdealUnmixed]
                        [isWeaklyGVD, IsIdealUnmixed]
                Headline
                        optional argument for GVD methods
                Description
                        Text
                                Whether the input ideal is unmixed, if known. If unknown, this is
                                checked.
                SeeAlso
                        isGVD
                        isLexCompatiblyGVD
                        isWeaklyGVD
///


doc///
        Node
                Key
                        OnlyDegenerate
                        [findOneStepGVD, OnlyDegenerate]
                Headline
                        optional argument for findOneStepGVD
                Description
                        Text
                                Set to {\tt true} to restrict the output of @TO oneStepGVD@ to return only
                                those indeterminates for which their geometric vertex decomposition is degenerate.
                                Default value {\tt false}.
                SeeAlso
                        findOneStepGVD
///


doc///
        Node
                Key
                        OnlyNondegenerate
                        [findOneStepGVD, OnlyNondegenerate]
                Headline
                        optional argument for findOneStepGVD
                Description
                        Text
                                Set to {\tt true} to restrict the output of @TO oneStepGVD@ to return only
                                those indeterminates for which their geometric vertex decomposition is nondegenerate.
                                Default value {\tt false}.
                SeeAlso
                        findOneStepGVD
///


doc///
        Node
                Key
                        RandomSeed
                        [findLexCompatiblyGVDOrder, RandomSeed]
                Headline
                        optional argument for findLexCompatiblyGVDOrder
                Description
                        Text
                                When brute forcing all possible orders, we shuffle their order upon each
                                method call. Set a seed for a consistent order.
                SeeAlso
                        findLexCompatiblyGVDOrder
///


doc///
        Node
                Key
                        Verbose
                        [isGVD, Verbose]
                        [isLexCompatiblyGVD, Verbose]
                        [isWeaklyGVD, Verbose]
                        [oneStepGVD, Verbose]
                Headline
                        optional argument for GVD methods
                Description
                        Text
                                If true, prints intermediate steps taken. Otherwise, prints nothing.
                SeeAlso
                        isGVD
                        isLexCompatiblyGVD
                        isWeaklyGVD
                        oneStepGVD
///

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--
-- TESTS
--
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Test CyI
--------------------------------------------------------------------------------


TEST///  -- [KR, Example 2.16]
R = QQ[x..z,w,r,s];
I = ideal( y*(z*s - x^2), y*w*r, w*r*(z^2 + z*x + w*r + s^2) );
assert( CyI(I, y) == ideal(x*z*w*r+z^2*w*r+w^2*r^2+w*r*s^2,w*r,x^2-z*s) )
///


TEST///  -- [KR, Example 4.10]
R = QQ[x..z,w,r,s];
I = ideal( y*(z*s - x^2), y*w*r, w*r*(x^2 + s^2 + z^2 + w*r) );
assert( CyI(I, y) == ideal(z*s-x^2, w*r) )
///


--------------------------------------------------------------------------------
-- Test findLexCompatiblyGVDOrder
--------------------------------------------------------------------------------


TEST///
R = QQ[x,y];
I = ideal(x^2 - y^2);
assert(findLexCompatiblyGVDOrder I == {false})
///


TEST///
R = QQ[x..z];
I = ideal(x-y, x-z);
assert( findLexCompatiblyGVDOrder(I, RandomSeed => 11) == {true, {z, y, x}} )
///


--------------------------------------------------------------------------------
-- Test findOneStepGVD
--------------------------------------------------------------------------------


TEST///
R = QQ[x..z];
I = ideal(x-y, y-z);
assert( findOneStepGVD I == {x,y,z} )
///


TEST///  -- [KR, Example 2.16]
R = QQ[x..z,w,r,s];
I = ideal( y*(z*s - x^2), y*w*r, w*r*(z^2 + z*x + w*r + s^2) );
assert( findOneStepGVD I == {y} )
///


--------------------------------------------------------------------------------
-- Test getGVDIdeal
--------------------------------------------------------------------------------

-- [KR, Example 2.16]
TEST///
R = QQ[x,y,z,w,r,s]
I = ideal(y*(z*s - x^2), y*w*r, w*r*(z^2+z*x+w*r+s^2))
assert(getGVDIdeal(I, {{"C", y}, {"N", s}}) == {ideal(x*z*w*r+z^2*w*r+w^2*r^2+w*r*s^2,w*r,x^2-z*s), ideal(w*r)})
///


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
assert(isGVD I)
///


TEST///  -- [KR, Example 4.10]
R = QQ[x,y,z,w,r,s];
I = ideal(y*(z*s - x^2), y*w*r, w*r*(x^2+ z^2 + s^2 + w*r));
assert(not isGVD I)
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
assert(isGVD I)
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
assert(not isGVD I)
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
assert(isGVD I)
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
assert(not isGVD I)
///
-- ~0.75 seconds, might be as quick as we will get for a non-GVD Hessenberg patch ideal


--------------------------------------------------------------------------------
-- Test isLexCompatiblyGVD
--------------------------------------------------------------------------------


TEST///
R = QQ[x,y]
I = ideal(x^2 - y^2)
assert(not isLexCompatiblyGVD(I, {x,y}))
///


TEST///
R = QQ[x..z]
I = ideal(x-y,x-z)
assert(isLexCompatiblyGVD(I, {x,y,z}))
///


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
assert(isWeaklyGVD I)
///


TEST///  -- not GVD, w = (1,3,2,4), h = (3,3,4,4), will need to verify that it is Weakly GVD by hand
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
assert(isWeaklyGVD I)
///


--------------------------------------------------------------------------------
-- Test NyI
--------------------------------------------------------------------------------


TEST///  -- [KR, Example 2.16]
R = QQ[x..z,w,r,s];
I = ideal( y*(z*s - x^2), y*w*r, w*r*(z^2 + z*x + w*r + s^2) );
assert( NyI(I, y) == ideal(x*z*w*r+z^2*w*r+w^2*r^2+w*r*s^2) )
///


TEST///  -- [KR, Example 4.10]
R = QQ[x..z,w,r,s];
I = ideal( y*(z*s - x^2), y*w*r, w*r*(x^2 + s^2 + z^2 + w*r) );
assert( NyI(I, y) == ideal(x^2*w*r+w*r*s^2+z^2*w*r+w^2*r^2) )
///


--------------------------------------------------------------------------------
-- Test oneStepGVD
--------------------------------------------------------------------------------


TEST///  -- [KR, Example 2.16]
R = QQ[x..z,w,r,s];
I = ideal( y*(z*s - x^2), y*w*r, w*r*(z^2 + z*x + w*r + s^2) );
assert( oneStepGVD(I, y, VerifyDegenerate=>true) == {true, ideal(x*z*w*r+z^2*w*r+w^2*r^2+w*r*s^2,w*r,x^2-z*s), ideal(x*z*w*r+z^2*w*r+w^2*r^2+w*r*s^2), "nondegenerate"} )
///


TEST///  -- [KR, Example 4.10]
R = QQ[x..z,w,r,s];
I = ideal( y*(z*s - x^2), y*w*r, w*r*(x^2 + s^2 + z^2 + w*r) );
assert( oneStepGVD(I, y, VerifyDegenerate=>true) == {true, ideal(z*s-x^2, w*r), ideal(x^2*w*r+w*r*s^2+z^2*w*r+w^2*r^2), "nondegenerate"} )
///


--------------------------------------------------------------------------------
-- Test yInit
--------------------------------------------------------------------------------


TEST///  -- [KR, Example 2.16]
R = QQ[x..z,w,r,s];
I = ideal( y*(z*s - x^2), y*w*r, w*r*(z^2 + z*x + w*r + s^2) );
assert( yInit(I, y) == ideal(x*z*w*r+z^2*w*r+w^2*r^2+w*r*s^2,y*w*r,y*x^2-y*z*s) )
///


end--
