-- -*- coding: utf-8 -*-

newPackage(
        "GeometricDecomposabilityExperimental",
        Version => "1.2.1",
        Date => "June 21, 2023",
        Headline => "A package to check whether ideals are geometrically vertex decomposable",
        Authors => {
                {
                Name => "Mike Cummings",
                Email => "cummim5@mcmaster.ca",
                HomePage => "https://math.mcmaster.ca/~cummim5/"
                },
                {
                Name => "Adam Van Tuyl",
                Email => "vantuyl@math.mcmaster.ca",
                HomePage => "https://ms.mcmaster.ca/~vantuyl/"
                }
                },
        Keywords => {"Commutative Algebra"},
        PackageImports => {"Depth", "PrimaryDecomposition", "ThreadedGB"},
        DebuggingMode => true  -- remove this later
        )

export {
        -- methods
        "CyI",
        "findLexCompatiblyGVDOrders",
        "findOneStepGVD",
        "getGVDIdeal",
        "isGeneratedByIndeterminates",
        "isGVD",
        "isLexCompatiblyGVD",
        "isUnmixed",
        "isWeaklyGVD",
        "NyI",
        "yInit",

        -- options
        "AllowSub",
        "CheckCM",
        "CheckDegenerate",
        "CheckUnmixed",
        "IsIdealHomogeneous",
        "IsIdealUnmixed",
        "OnlyDegenerate",
        "OnlyNondegenerate"
        };

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--
-- METHODS
--
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------

CyI = method(
        TypicalValue => Ideal, 
        Options => {CheckUnmixed => true}
        )
CyI(Ideal, RingElement) := opts -> (I, y) -> (oneStepGVD(I, y, CheckUnmixed=>opts.CheckUnmixed))_1;

--------------------------------------------------------------------------------

findLexCompatiblyGVDOrders = method(
        TypicalValue => List, 
        Options => {CheckUnmixed => true}
        )
findLexCompatiblyGVDOrders(Ideal) := opts -> I -> (
        if isGVDBaseCase I then (
                return permutations gens ring I;
                );
        try (
                orders := sort lexOrderHelper({I}, {}, CheckUnmixed=>opts.CheckUnmixed);
                truncatedOrders := recursiveFlatten orders;
                )
        then (
                allLexOrders := permutations gens ring I;
                validLexOrders := select(allLexOrders, lexOrder -> inTruncatedList(lexOrder, truncatedOrders) );
                return validLexOrders;
                )
        else (
                return {};
        )
        )

--------------------------------------------------------------------------------

findOneStepGVD = method(
        TypicalValue => List, 
        Options => {
                AllowSub => false,  -- not yet implemented
                CheckUnmixed => true, 
                OnlyNondegenerate => false, 
                OnlyDegenerate => false
                }
        )
findOneStepGVD(Ideal) := opts -> I -> (
        -- returns a list of indeterminates for which there exists a one-step geometric vertex decomposition

        if opts.OnlyNondegenerate and opts.OnlyDegenerate then (
                error("a geometric vertex decomposition cannot be both degenerate and nondegenerate");
                return {};
                );


        getGBandCNideals := (I, y) -> (
                -- returns {GB, CyI, NyI}
                R := ring I;
                cr := coefficientRing R;
                indeterminates := switch(0, index y, gens ring y);  -- assumes that y and I are "from" the same ring

                S := (cr) monoid([indeterminates, MonomialOrder=>Lex]);  -- ring that has lex order with y > all other variables
                J := sub(I, S);
                z := sub(y, S);
                grobnerBasis := first entries gens gb J;

                gensN := delete(0, apply(grobnerBasis, g -> isInN(g, z)));
                NyI := ideal(gensN);

                gensC := delete(true, flatten(apply(grobnerBasis, g -> isInC(g, z))));
                CyI := ideal(delete(false, gensC));

                return {grobnerBasis, CyI, NyI};
                );

        
        CheckDegeneracy := (C, N, D, ND) -> (
                -- assumes either D (onlyDegenerate) xor ND (onlyNondegenerate)
                isDegenerate := (C == 1) or (radical C == radical N);
                if D then (
                        return isDegenerate
                        );
                
                if ND then (
                        return not isDegenerate
                        );
                );

        
        easyCaseHandler := (I, y, D, ND) -> (
                -- in the "easy" case but where degeneracy must be checked, GB/C/N are not already computed, 
                -- so we combine the previous two functions here

                o := getGBandCNideals(I, y);
                C := o_1;
                N := o_2;

                return CheckDegeneracy(C, N, D, ND)
                );
        

        satisfiesOneStep := (I, y, D, ND) -> (
                o := getGBandCNideals(I, y);
                grobnerBasis := o_0;
                C := o_1;
                N := o_2;
                
                grobnerLeadTerms := apply(grobnerBasis, f -> leadTerm f);
                hasOneStep := areGensSquarefreeInY(grobnerLeadTerms, sub(y, ring C));  -- whether I has a geometric vertex decomposition with respect to y

                -- check degeneracy condition, if specified
                if hasOneStep and (ND or D) then (
                        isDegenerate := (CyI == 1) or (radical CyI == radical NyI);
                        if D then (
                                return isDegenerate
                                );
                        
                        if ND then (
                                return not isDegenerate
                                );
                        );

                return hasOneStep;
                );

        R := ring I;
        indets := support I;

        -- we use [KR, Lemma 2.6] and [KR, Lemma 2.12]

        -- first get the indets with respect to which the ideal is "clearly" squarefree 
        -- the variables y such that y^2 does not divide any term of any generator of I
        gensTerms := flatten apply(first entries gens I, f -> terms f);
        clearlySquarefreeIndets := select(indets, y -> areGensSquarefreeInY(gensTerms, y));

        remainingIndets := toList( set(indets) - set(clearlySquarefreeIndets) );
        -- for the remaining indets, compute a Gröbner basis and check whether the initial terms
        -- are squarefree with respect to each
        -- in the case that OnlyDegenerate or OnlyNondegenerate is specified, then check these conditions
        validRemaining := select(remainingIndets, y -> satisfiesOneStep(I, y, opts.OnlyDegenerate, opts.OnlyNondegenerate));


        -- check the degeneracy conditions, if specified
        if (opts.OnlyDegenerate or opts.OnlyNondegenerate) then (
                clearlyDegenerateIndets := select(clearlySquarefreeIndets, y -> easyCaseHandler(I, y));
                return reverse sort toList( set(clearlyDegenerateIndets) + set(validRemaining) );
        );

        return reverse sort toList( set(clearlySquarefreeIndets) + set(validRemaining) );
        )

--------------------------------------------------------------------------------

getGVDIdeal = method(
        TypicalValue => List, 
        Options => {CheckUnmixed => true}
        )
getGVDIdeal(Ideal, List) := opts -> (I, L) -> (
        CNs := new HashTable from {
                "C" => CyI,
                "N" => NyI
                };
        return accumulate( (i, j) -> CNs#(j_0)(i, j_1, CheckUnmixed=>opts.CheckUnmixed) , prepend(I, L) );  -- last entry is the desired ideal
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
isGVD = method(
        TypicalValue => Boolean, 
        Options => {
                AllowSub => false,  -- not yet implemented
                CheckCM => "once", 
                CheckUnmixed => true, 
                IsIdealHomogeneous => false, 
                IsIdealUnmixed => false, 
                Verbose => false
                }
        )
isGVD(Ideal) := opts -> I -> (

        if not instance(opts.CheckCM, String) then (
                error "value of CheckCM must be a string";
                ) else (
                if not isSubset({opts.CheckCM}, {"always", "once", "never"}) then error ///unknown value of CheckCM, options are "once" (default), "always", "never"///;
                );

        R := ring I;
        printIf(opts.Verbose, toString I);

        if I == 0 then (printIf(opts.Verbose, "-- zero ideal"); return true);
        if I == 1 then (printIf(opts.Verbose, "-- unit ideal"); return true);
        if (isGeneratedByIndeterminates I) then (printIf(opts.Verbose, "-- generated by indeterminates"); return true);

        if opts.CheckUnmixed then (
                if not opts.IsIdealUnmixed then (
                        if not (isUnmixed I) then (printIf(opts.Verbose, "-- ideal is not unmixed"); return false);
                        );
                );

        x := opts.IsIdealHomogeneous or isHomogeneous(I);
        if opts.CheckCM == "once" or opts.CheckCM == "always" then (
                if x then (
                        if (not isCM(R/I)) then (printIf(opts.Verbose, "-- ideal is homogeneous but not Cohen-Macaulay") ; return false);
                        );
                );

        CMTable := new HashTable from {
                "always" => "always",
                "once" => "never",
                "never" => "never"
                };

        -- check all options for y which yield a one-step geometric vertex decomposition
        viableIndets := findOneStepGVD I;
        for y in viableIndets do (

                printIf(opts.Verbose, "-- decomposing with respect to " | toString y);

                (isValid, C, N) := oneStepGVD(I, y, CheckUnmixed=>opts.CheckUnmixed, Verbose=>opts.Verbose);
                if not isValid then continue;  -- go back to top of for loop

                printIf(opts.Verbose, "-- C = " | toString C);
                printIf(opts.Verbose, "-- N = " | toString N);

                CisGVD := isGVD(C, CheckCM=>CMTable#(opts.CheckCM), CheckUnmixed=>opts.CheckUnmixed, IsIdealHomogeneous=>x, IsIdealUnmixed=>true, Verbose=>opts.Verbose);
                NisGVD := isGVD(N, CheckCM=>CMTable#(opts.CheckCM), CheckUnmixed=>opts.CheckUnmixed, IsIdealHomogeneous=>x, IsIdealUnmixed=>true, Verbose=>opts.Verbose);

                if (CisGVD and NisGVD) then return true;
                );

        -- if we are here, no choice of y worked
        return false;
        )

--------------------------------------------------------------------------------

-- [KR, Definition 2.11]
isLexCompatiblyGVD = method(
        TypicalValue => Boolean, 
        Options => {
                CheckCM => "once", 
                CheckUnmixed => true, 
                IsIdealHomogeneous => false, 
                IsIdealUnmixed => false, 
                Verbose => false
                }
        )
isLexCompatiblyGVD(Ideal, List) := opts -> (I, indetOrder) -> (
        if not instance(opts.CheckCM, String) then (
                error "value of CheckCM must be a string";
                ) else (
                if not isSubset({opts.CheckCM}, {"always", "once", "never"}) then error ///unknown value of CheckCM, options are "once" (default), "always", "never"///;
                );

        R := ring I;
        printIf(opts.Verbose, toString I);

        if I == 0 then (printIf(opts.Verbose, "-- zero ideal"); return true);
        if I == 1 then (printIf(opts.Verbose, "-- unit ideal"); return true);
        if (isGeneratedByIndeterminates I) then (printIf(opts.Verbose, "-- generated by indeterminates"); return true);

        supportIndets := support I;
        trimmedOrder := select(indetOrder, i -> member(sub(i, R), supportIndets));

        if opts.CheckUnmixed then (
                if not opts.IsIdealUnmixed then (
                        if not (isUnmixed I) then (printIf(opts.Verbose, "-- ideal is not unmixed"); return false);
                        );
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

        (isValid, C, N) := oneStepGVD(I, y, CheckUnmixed=>opts.CheckUnmixed, Verbose=>opts.Verbose);
        if not isValid then return false;  -- order didn't work

        printIf(opts.Verbose, "-- C = " | toString C);
        printIf(opts.Verbose, "-- N = " | toString N);

        CisGVD := isLexCompatiblyGVD(C, remainingOrder, CheckCM=>CMTable#(opts.CheckCM), CheckUnmixed=>opts.CheckUnmixed, IsIdealHomogeneous=>x, IsIdealUnmixed=>true, Verbose=>opts.Verbose);
        NisGVD := isLexCompatiblyGVD(N, remainingOrder, CheckCM=>CMTable#(opts.CheckCM), CheckUnmixed=>opts.CheckUnmixed, IsIdealHomogeneous=>x, IsIdealUnmixed=>true, Verbose=>opts.Verbose);

        return (CisGVD and NisGVD);
        )

--------------------------------------------------------------------------------

isUnmixed = method(TypicalValue => Boolean)
isUnmixed(Ideal) := I -> (
        R := ring I;
        D := primaryDecomposition I;
        d := apply(D, i -> dim(R/i));
        return all(apply(d, i -> (i == d_0)), i -> i);  -- list contains only true values
        )

--------------------------------------------------------------------------------

-- [KR, Definition 4.6]
isWeaklyGVD = method(
        TypicalValue => Boolean, 
        Options => {
                CheckUnmixed => true, 
                IsIdealUnmixed => false, 
                Verbose => false
                }
        )
isWeaklyGVD(Ideal) := opts -> I -> (
        R := ring I;
        printIf(opts.Verbose, toString I);

        if I == 0 then (printIf(opts.Verbose, "-- zero ideal"); return true);
        if I == 1 then (printIf(opts.Verbose, "-- unit ideal"); return true);
        if (isGeneratedByIndeterminates I) then (printIf(opts.Verbose, "-- generated by indeterminates"); return true);

        if opts.CheckUnmixed then (
                if not opts.IsIdealUnmixed then (
                        if not (isUnmixed I) then (printIf(opts.Verbose, "-- ideal is not unmixed"); return false);
                        );
                );

        viableIndets := findOneStepGVD I;

        -- check all options for y until one works
        for y in viableIndets do (

                printIf(opts.Verbose, "-- decomposing with respect to " | toString y);

                oneStep := oneStepGVD(I, y, CheckDegenerate=>true, CheckUnmixed=>opts.CheckUnmixed, Verbose=>opts.Verbose);
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
                        if isWeaklyGVD(N, CheckUnmixed=>opts.CheckUnmixed, IsIdealUnmixed=>true, Verbose=>opts.Verbose) then return true else continue;

                        ) else (
                        -- nondegenerate case
                        if not (radical(N, Unmixed=>true) == N and isCM(ring N/N)) then continue;
                        if isWeaklyGVD(C, CheckUnmixed=>opts.CheckUnmixed, IsIdealUnmixed=>true, Verbose=>opts.Verbose) then return true else continue;
                        )
                );

        -- if we are here, no choice of y worked
        return false;
        )

--------------------------------------------------------------------------------

NyI = method(
        TypicalValue => Ideal, 
        Options => {CheckUnmixed => true}
        )
NyI(Ideal, RingElement) := opts -> (I, y) -> (oneStepGVD(I, y, CheckUnmixed=>opts.CheckUnmixed))_2;

--------------------------------------------------------------------------------

oneStepGVD = method(
        TypicalValue => Sequence, 
        Options => {
                AllowSub => false,
                CheckDegenerate => false, 
                CheckUnmixed => true, 
                Verbose => false
                }
        )
oneStepGVD(Ideal, RingElement) := opts -> (I, y) -> (

        if opts.AllowSub and opts.CheckDegenerate then (
                print("Caution: A (non-)degenerate geometric vertex decomposition---and hence, the notion of weakly GVD---is not known to be compatible with allowing substitutions");
                );

        -- set up the rings
        indeterminates := switch(0, index y, gens ring y);
        remainingIndets := drop(gens ring y, {index y, index y});
        cr := coefficientRing ring I;

        givenRing := ring I;
        lexRing := (cr) monoid([indeterminates, MonomialOrder=>Lex]);
        contractedRing := (cr) monoid([remainingIndets]);

        -- pull everthing into the new rings and get a (reduced) Gröbner basis
        J := sub(I, lexRing);
        z := sub(y, lexRing);
        G := first entries gens gb J;

        -- check whether the intersection condition holds
        isValid := isValidOneStep(G, z, opts.AllowSub);
        if not isValid then (
                printIf(opts.Verbose, "Warning: not a valid geometric vertex decomposition");
                );

        -- get N_{y,I}
        gensN := delete(0, apply(G, g -> isInN(g, z)));
        NyI := ideal(gensN);

        -- get C_{y, I}
        gensC := delete(true, flatten(apply(G, g -> isInC(g, z))));
        CyI := ideal(delete(false, gensC));

        C := sub(CyI, contractedRing);
        N := sub(NyI, contractedRing);

        -- check unmixed & degenerate as needed, and return
        if opts.CheckUnmixed and opts.CheckDegenerate then (
                unmixedIdeals := unmixedCheck(C, N, opts.Verbose);
                degeneracyStatus := degeneracyCheck(C, N);
                return (isValid and unmixedIdeals, C, N, degeneracyStatus);
                );
        if opts.CheckUnmixed then (  -- not needed to CheckDegenerate
                unmixedIdeals1 := unmixedCheck(C, N, opts.Verbose);
                return (isValid and unmixedIdeals1, C, N);
                );
        if opts.CheckDegenerate then ( -- not needed to CheckUnmixed
                degeneracyStatus1 := degeneracyCheck(C, N);
                return (isValid, C, N, degeneracyStatus1);
                );
        
        -- otherwise, we don't need not check unmixed nor degeneracy
        return (isValid, C, N);
        )

--------------------------------------------------------------------------------

-- [KMY, Section 2.1]
yInit = method(TypicalValue => Ideal)
yInit(Ideal, RingElement) := (I, y) -> (
        givenRing := ring I;

        -- set up the ring
        indeterminates := switch(0, index y, gens ring y);
        cr := coefficientRing ring I;

        initYFormRing := (cr) monoid([indeterminates, MonomialOrder=>ProductOrder{1, #indeterminates - 1}]);

        -- get the ideal of initial y-forms using the product order
        I = sub(I, initYFormRing);
        y = sub(y, initYFormRing);
        inyFormIdeal := ideal leadTerm(1,I);

        return sub(inyFormIdeal, givenRing);
        )

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

--** METHODS (Hidden from users, not exported)


areGensSquarefreeInY = method(TypicalValue => Boolean)
areGensSquarefreeInY(List, RingElement) := (L, y) -> (
        -- L a list of polynomials (e.g., generators of some ideal), and y an indeterminate in the ring
        -- returns true if and only if ideal(L) is squarefre in y, that is, if y^2 does not divide any term of any of the polynomials

        return all( apply(L, m -> isSquarefreeInY(m, y)), i->i );
        )


-- check if C_{y, I} and N_{y, I} form a degenerate (or not) geometric vertex decomposition
degeneracyCheck = method(TypicalValue => String)
degeneracyCheck(Ideal, Ideal) := (C, N) -> (
        -- degenerate if C == 1 or radical C == radical N
        if C == 1 then return "degenerate";

        radC := radical(C, Unmixed=>true);
        radN := radical(N, Unmixed=>true);
        if (radC == radN) then return "degenerate";

        -- if we are here, we are nondegenerate
        return "nondegenerate";
        )


isGVDBaseCase = method(TypicalValue => Boolean)
isGVDBaseCase(Ideal) := I -> (
        return (I == 1 or I == 0 or isGeneratedByIndeterminates(I));
        )


isIdealSquarefreeInY = method(TypicalValue => Boolean)
isIdealSquarefreeInY(Ideal, RingElement) := (I, y) -> (
        -- returns true if and only if I is squarefree in y, that is: if and only if
        -- y^2 does not divide any term of a Grobner basis of I with respect to a y-compatible monomial order 
        -- we use lex with y > all other variables

        R := ring I;
        cr := coefficientRing R;
        indeterminates := switch(0, index y, gens ring y);  -- assumes that y and I are "from" the same ring

        S := (cr) monoid([indeterminates, MonomialOrder=>Lex]);  -- ring that has lex order with y > all other variables
        J := sub(I, S);
        z := sub(y, S);
        grobnerLeadTerms := first entries gens leadTerm J;
        return areGensSquarefreeInY(grobnerLeadTerms, z);
        )


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


intersectLists = method(TypicalValue => List)
intersectLists(List) := L -> (
        -- L is a list of lists
        S := for l in L list (set l);
        return toList fold(intersectSets, S)
        )


intersectSets = method(TypicalValue => Set)
intersectSets(Set, Set) := (S1, S2) -> (
        return S1 * S2;
        )


inTruncatedList = method(TypicalValue => Boolean)
inTruncatedList(List, List) := (L, LL) -> (
        -- LL is a list of lists
        -- return True if: for some list l of length n in LL, the first n terms of L are exactly l
        for l in LL do (
                n := #l;
                if l == take(L, n) then return true;
                );
        return false;
        )


getQ = method(TypicalValue => RingElement)
getQ(RingElement, RingElement) := (f, y) -> (
        -- f is of the form q*y^d+r, return q
        r := sub(f, y=>0);
        qy := f - r;
        return sub(qy, y=>1);
        )

lexOrderHelper = method(TypicalValue => List, Options => {CheckUnmixed => true})
lexOrderHelper(List, List) := opts -> (idealList, order) -> (
        -- remove ideals that are trivially GVD
        nontrivialIdeals := select(idealList, i -> not isGVDBaseCase i);
        -- if there are none left, return the order
        if (#nontrivialIdeals) == 0 then (
                return order;
                );

        -- for each ideal, get the indets which form a oneStepGVD
        possibleIndets := apply(nontrivialIdeals, i -> findOneStepGVD(i, CheckUnmixed=>opts.CheckUnmixed));
        commonPossibleIndets := intersectLists possibleIndets;
        if commonPossibleIndets == {} then return;

        -- for each variable, compute the C and N ideals
        nextIdeals := for y in commonPossibleIndets list (
                flatten apply( nontrivialIdeals, i -> (
                        oneStep := oneStepGVD(i, y);
                        {oneStep_1, oneStep_2}
                        ))
                );

        L := for m from 0 to (#commonPossibleIndets)-1 list (
                lexOrderHelper(nextIdeals#m, append(order, commonPossibleIndets#m))
                );
        return L;
        )


isSquarefreeInY = method()
isSquarefreeInY(RingElement, RingElement) := (m, y) -> (
        -- m a monomial, y an indeterminate
        -- returns true if and only if m is squarefree in y
        return not (m % y^2 == 0)
        )


-- determine whether the one-step geometric vertex decomposition holds
-- uses [KR, Lemmas 2.6 and 2.12] and generalizations thereof
isValidOneStep = method(TypicalValue => Boolean)
isValidOneStep(List, RingElement, Boolean) := (G, y, allowingSub) -> (
        -- G is a list, whose elements form a reduced Gröbner basis

        -- analyze the powers of y appearing in the Gröbner basis
        gbTerms := flatten apply(G, f -> terms f);
        yDegrees := unique apply(gbTerms, m -> degree(y, m));
        yMaxDegree := max yDegrees;

        if not allowingSub then (
                return yMaxDegree == 1;
                );

        yOtherDegrees := delete(0, delete(yMaxDegree, yDegrees)); -- all degrees of y in the GB that are not 0 and not the highest degree
        noOtherYDegrees := (#yOtherDegrees == 0);
        return noOtherYDegrees;
        )


printIf = method()
printIf(Boolean, String) := (bool, str) -> (
        if bool then print str;
        )

        recursiveFlatten = method(TypicalValue => List)
        recursiveFlatten(List) := L -> (
                Lstr := toString L;
                if Lstr#2 == "{" then (
                        return recursiveFlatten flatten L;
                        )
                else (
                        return L;
                        )
                )


unmixedCheck = method(TypicalValue => Boolean)
unmixedCheck(Ideal, Ideal, Boolean) := (C, N, verb) -> (
        isUnmixedC := isUnmixed C;
        isUnmixedN := isUnmixed N;

        bothUnmixed := (isUnmixedC and isUnmixedN);

        if not isUnmixedC then (
                printIf(verb, "Warning: CyI is not unmixed");
                );
        if not isUnmixedN then (
                printIf(verb, "Warning: NyI is not unmixed");
                );

        return bothUnmixed;
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
                        GeometricDecomposabilityExperimental

                Headline
                        a package to check whether ideals are geometrically vertex decomposable

                Description
                        Text

                                This package includes routines to check whether an ideal is
                                geometrically vertex decomposable.

                                Geometrically vertex
                                decomposable ideals can be viewed as a generalization of the properties
                                of the Stanley-Reisner ideal of a vertex decomposable simplicial complex.
                                This family of ideals is based upon the geometric vertex
				decomposition property defined by Knutson, Miller, and Yong [KMY]. Klein and Rajchgot
                                then gave a recursive definition for
				geometrically vertex decomposable ideals in [KR] using this notion.

                                An unmixed ideal $I$ in a polynomial ring $R$ is geometrically vertex
                                decomposable if it is the zero ideal, the unit ideal, an ideal generated
                                by indeterminates, or if there is a indeterminate $y$ of $R$ such that
                                two ideals $C_{y,I}$ and $N_{y,I}$ constructed from $I$ are
                                both geometrically vertex decomposable. For the complete definition, see
                                @TO isGVD@.

                                Observe that a geometrically vertex decomposable ideal is recursively
                                defined. The complexity of verifying that an ideal is geometrically
                                vertex decomposable will increase as the number of indeterminates
                                appearing in the ideal increases.

                Acknowledgement
                        We thank S. Da Silva, P. Klein, M. Harada, and J. Rajchgot for feedback and suggestions. 
                        Cummings was partially supported by an NSERC USRA and CGS-M and the Milos Novotny Fellowship. 
                        Van Tuyl's research is partially supported by NSERC Discovery Grant 2019-05412.

                References

                        [CDSRVT] Mike Cummings, Sergio Da Silva, Jenna Rajchgot, and Adam Van Tuyl.
                        Geometric Vertex Decomposition and Liaison for Toric Ideals of
                        Graphs. To appear in Algebraic Combinatorics, preprint available at @arXiv "2207.06391"@ (2022).

                        [DSH] Sergio Da Silva and Megumi Harada. Geometric vertex decomposition, Gröbner bases, and Frobenius 
                        splittings for regular nilpotent Hessenberg Varieties. 
                        To appear in Transformation Groups, preprint available at @arXiv "2207.08573"@ (2022).

                        [KMY] Allen Knutson, Ezra Miller, and Alexander Yong. Gröbner Geometry of Vertex
                        Decompositions and of Flagged Tableaux. J. Reine Angew. Math. 630 (2009) 1–31.

                        [KR] Patricia Klein and Jenna Rajchgot. Geometric Vertex Decomposition and
                        Liaison. Forum of Math, Sigma, 9 (2021) e70:1-23.

                        [SM] Hero Saremi and Amir Mafi. Unmixedness and Arithmetic Properties of
                        Matroidal Ideals. Arch. Math. 114 (2020) 299–304.

                Subnodes
                        AllowSub
                        CheckCM
                        CheckDegenerate
                        CheckUnmixed
                        CyI
                        findLexCompatiblyGVDOrders
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
                        :Ideal

                Caveat
                        This method is a shortcut to extract the ideal $C_{y,I}$ as computed
                        in @TO oneStepGVD@. That is, to compute $C_{y,I}$, {\tt oneStepGVD} is called in the background.
                        As a result, work is also done in the background to compute $N_{y,I}$ at
                        the same time, and as such, we encourage calling {\tt oneStepGVD}
                        directly if we want both the $C_{y,I}$ and $N_{y,I}$ ideals to avoid
                        performing the same computation twice.

	        Description
	                Text
			        Let $y$ be a variable of the polynomial ring $R = k[x_1,\ldots,x_n]$. A monomial ordering $<$ on $R$ is said to be
                                {\it $y$-compatible} if the initial term of $f$ satisfies ${\rm in}_<(f) = {\rm in}_<({\rm in}_y(f))$ for all $f \in R$.
				Here, ${\rm in}_y(f)$ is the {\it initial $y$-form} of $f$, that is, if $f = \sum_i \alpha_iy^i$ and $\alpha_d \neq 0$
				but $\alpha_t = 0$ for all $t >d$, then ${\rm in}_y(f) = \alpha_d y^d$.

                                Given an ideal $I$ and a $y$-compatible monomial ordering $<$, let $G(I) = \{ g_1,\ldots,g_m\}$ be a Gröbner basis of $I$ with respect to this
                                ordering.  For $i=1,\ldots,m$, write $g_i$ as $g_i = y^{d_i}q_i + r_i$, where $y$ does not divide any term of $q_i$;
                                that is, ${\rm in}_y(g_i) = y^{d_i}q_i$.   Given this setup, the ideal $C_{y,I}$ is given by
                                $$C_{y,I} = \langle q_1,\ldots,q_m\rangle$$
			        This functions  takes an ideal $I$ and variable $y$, and returns $C_{y,I}$.

                                The ideal $C_{y,I}$ does not depend upon the choice of the Gröbner basis or
                        	a particular $y$-compatible order (see comment after [KR, Definition 2.3]).
				When computing $C_{y,I}$ we use a lexicographical ordering
                        	on $R$ where $y > x_j$ for all $i \neq j$ if $y = x_i$ since this gives us a $y$-compatible order.

                                The ideal $I$ in the example below is the edge ideal of the complete graph $K_4$.
                                For more on edge ideals, see the EdgeIdeals package.

                        Example
                                R = QQ[a,b,c,d];
                                I = ideal(a*b, a*c, a*d, b*c, b*d, c*d); -- edge ideal of the complete graph K_4, a chordal graph
                                CyI(I, b)
				L = oneStepGVD(I, b);
			        L_1 == CyI(I, b) -- CyI is the second element in the list given by oneStepGVD
    	    	References
		        [KR] P. Klein and J. Rajchgot. Geometric Vertex Decomposition and
                        Liaison. Forum of Math, Sigma, 9 (2021) e70:1-23.
                SeeAlso
                        CheckUnmixed
                        getGVDIdeal
                        NyI
                        oneStepGVD
///


doc///
        Node
                Key
                        findLexCompatiblyGVDOrders
                        (findLexCompatiblyGVDOrders, Ideal)
                Headline
                        finds all lexicographic monomial orders $<$ such that the ideal is $<$-compatibly geometrically vertex decomposable
                Usage
                        findLexCompatiblyGVDOrders I
                Inputs
                        I:Ideal
                Outputs
                        :List
                                if no order exists, returns {}, otherwise returns {\tt L}, a list containing all the lexicographical orders which work

                Description

                        Text

                                An ideal $I$ is $<$-compatibly geometrically vertex decomposable if
                                there exists a (lexicographic) order $<$ such that $I$ is geometrically vertex
                                decomposable and for every (one-step) geometric vertex decomposition, we
                                pick $y$ to be the most expensive indeterminate remaining in the ideal according
                                to $<$ [KR, Definition 2.11].
                                For the definition of a (one-step) geometric vertex decomposition, see @TO oneStepGVD@.

                                This method computes all possible lex orders $<$ for which the ideal $I$ is $<$-compatibly
                                geometrically vertex decomposable.

			Example
                                R = QQ[x,y,z];
                                I = ideal(x-y, x-z);
                                findLexCompatiblyGVDOrders I

                        Text
                                The ideal in the following example is not square-free with respect to
                                any indeterminate, so no one-step geometric vertex decomposition exists.

                        Example
			        R = QQ[x,y];
                                I = ideal(x^2-y^2);
				findLexCompatiblyGVDOrders I

                Caveat
                        In the ring $k[x_1, \ldots, x_n]$, there are $n!$ possible lexicographic
                        monomial orders, so this function can be computationally expensive.


		References
		        [KR] P. Klein and J. Rajchgot. Geometric Vertex Decomposition and
                        Liaison. Forum of Math, Sigma, 9 (2021) e70:1-23.

                SeeAlso
                        CheckUnmixed
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
                Inputs
                        I:Ideal
                Outputs
                        :List

                Description
                        Text
                                Returns a list containing the $y$ for which there exists a @TO oneStepGVD@.  In other words, a list
				of all the variables $y$ that satisfy ${\rm in}_y(I) = C_{y,I} \cap (N_{y,I} + \langle y \rangle)$.
                                All indeterminates $y$ which appear in the ideal are checked.

                                The results [KR, Lemma 2.6] and [KR, Lemma 2.12] are used to check whether $I$ has a geometric vertex 
                                decomposition with respect to each indeterminate $y$.
                                First, for each indeterminate $y$ appearing in the ideal, we check whether the given generators of the ideal
                                are squarefree in $y$.
                                That is, if $y^2$ does not divide any term of any generator.
                                Note that this is a sufficient but not necessary condition.
                                For the indeterminates $z$ that do not satisfy this sufficient condition, we compute a Gröbner of $I$ 
                                with respect to a $z$-compatible monomial order, and repeat the squarefree-check for the entries of this
                                Gröbner basis.

                        Example
                                R = QQ[x,y,z]
                                I = ideal(x-y, x-z)
                                findOneStepGVD I

                        Text
                                The following example is [KR, Example 2.16]. The variable $b$ is
                                the only indeterminate for which there exists a geometric vertex decomposition.

                        Example
                                R = QQ[a..f]
                                I = ideal(b*(c*f - a^2), b*d*e, d*e*(c^2+a*c+d*e+f^2))
                                findOneStepGVD I

                References
		        [KR] P. Klein and J. Rajchgot. Geometric Vertex Decomposition and
                        Liaison. Forum of Math, Sigma, 9 (2021) e70:1-23.

                SeeAlso
                        AllowSub
                        CheckUnmixed
                        oneStepGVD
                        OnlyDegenerate
                        OnlyNondegenerate
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
                        :List
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
				variable $y_3$, and finding either the $C$ or $N$ ideals of these ideals.

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
                        CheckUnmixed
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
                        :Boolean
                Description
                        Text
                                An ideal is generated by indeterminates if the generators are a
                                (possibly empty) subset of the indeterminates in the ring.

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
                        [isGVD, Verbose]
                Headline
                        checks whether an ideal is geometrically vertex decomposable
                Usage
                        isGVD I
                Inputs
                        I:Ideal
                Outputs
                        :Boolean
                Description
                        Text
                                This function tests whether a given ideal is geometrically vertex decomposable.
		                Geometrically vertex decomposable ideals are based upon the geometric vertex
				decomposition defined by Knutson, Miller, and Yong [KMY].  Using geometric
				vertex decomposition, Klein and Rajchgot gave a recursive definition for
				geometrically vertex decomposable ideals in [KR, Definition 2.7].  This definition generalizes the properties
				of a square-free monomial ideal whose associated simplicial complex is vertex decomposable.

                                We include the definition here.
				Let $y$ be a variable of the polynomial ring $R = k[x_1,\ldots,x_n]$. A monomial ordering $<$ on $R$ is said to be
                                {\it $y$-compatible} if the initial term of $f$ satisfies ${\rm in}_<(f) = {\rm in}_<({\rm in}_y(f))$ for all $f \in R$.  Here,
				${\rm in}_y(f)$ is the {\it initial $y$-form} of $f$, that is, if $f = \sum_i \alpha_iy^i$ and $\alpha_d \neq 0$
				but $\alpha_t = 0$ for all $t >d$, then ${\rm in}_y(f) = \alpha_d y^d$.
				We set ${\rm in}_y(I) = \langle {\rm in}_y(f) ~|~ f \in I \rangle$ to be the ideal generated by all the initial $y$-forms in $I$.




                                Given an ideal $I$ and a $y$-compatible monomial ordering $<$, let $G(I) = \{ g_1,\ldots,g_m\}$ be a Gröbner basis of $I$ with respect to this
                                ordering.  For $i=1,\ldots,m$, write $g_i$ as $g_i = y^{d_i}q_i + r_i$, where $y$ does not divide any term of $q_i$;
                                that is, ${\rm in}_y(g_i) = y^{d_i}q_i$.   Given this setup, we define two ideals:
                                $$C_{y,I} = \langle q_1,\ldots,q_m\rangle$$
                                and
                                $$N_{y,I} = \langle q_i ~|~ d_i = 0 \rangle.$$
                                Recall that an ideal $I$ is {\it unmixed} if all of the associated primes of $I$ have the same height.

                                An ideal $I$ of $R =k[x_1,\ldots,x_n]$ is {\it geometrically vertex decomposable} if $I$ is unmixed and

                                (1)  $I = \langle 1 \rangle$, or $I$ is generated by a (possibly empty) subset of variables of $R$, or

                                (2) there is a variable $y = x_i$ in $R$ and a $y$-compatible monomial ordering $<$ such that
                                        $${\rm in}_y(I) = C_{y,I} \cap (N_{y,I} + \langle y \rangle),$$
                                        and the contractions of the
                                        ideals $C_{y,I}$ and $N_{y,I}$ to the ring
                                        $k[x_1,\ldots,\hat{y},\ldots,x_n]$ are geometrically
                                        vertex decomposable.

                        	{\it NOTE:}  The ideals $C_{y,I}$ and $N_{y,I}$ do not depend upon the choice of the Gröbner basis or
                        	a particular $y$-compatible order (see comment after [KR, Definition 2.3]).
                        	When computing $C_{y,I}$ and $N_{y,I}$ we use a lexicographical ordering
                        	on $R$ where $y > x_j$ for all $i \neq j$ if $y = x_i$ since this gives us a $y$-compatible order.

                        Example
                	        R = QQ[a,b,c,d]
                		f = 3*a*b + 4*b*c+ 16*a*c + 18*d
                		i = ideal f
                		isGVD i

                        Text
                	        Square-free monomial ideals that are geometrically vertex decomposable are precisely those square-free monomial ideals
                		whose associated simplicial complex are vertex decomposable [KR, Proposition 2.9].
				The edge ideal of a chordal graph corresponds to a simplicial
                		complex that is vertex decomposable (for more, see the EdgeIdeals package).  The option {\tt Verbose} shows the intermediate steps; in particular, {\tt Verbose}
				displays what variable is being used to test a decomposition, as well as the ideals
				$C_{y,I}$ and $N_{y,I}$.


                        Example
                                R = QQ[a,b,c,d]
                                i = ideal(a*b, a*c, a*d, b*c, b*d, c*d) -- edge ideal of a complete graph K_4, a chordal graph
                                isGVD(i, Verbose=>true)

                        Text
                                The following is an example of a toric ideal of graph that is geometrically vertex decomposable, and another example
                		of a toric ideal of a graph that is not geometrically vertex decomposable. The second ideal is not Cohen-Macaulay, so it
                		cannot be geometrically vertex decomposable [KR, Corollary 4.5].
                                For background on toric ideals of graphs, see [CDSRVT, Section 3].

                        Example
                	        R = QQ[e_1..e_7]
                		i = ideal(e_2*e_7-e_5*e_6, e_1*e_4-e_2*e_3) -- the toric ideal of a graph
                		isGVD i
                	        R = QQ[e_1..e_10]
                		i = ideal(e_1*e_4-e_2*e_3, e_2^2*e_7*e_8*e_9-e_4^2*e_5*e_6*e_10, e_1*e_2*e_7*e_8*e_9-e_3*e_4*e_5*e_6*e_10, e_1^2*e_7*e_8*e_9-e_3^2*e_5*e_6*e_10)
                		isGVD i
		References
                        [CDSRVT] M. Cummings, S. Da Silva, J. Rajchgot, and A. Van Tuyl.
                        Geometric Vertex Decomposition and Liaison for Toric Ideals of
                        Graphs. Preprint, @arXiv "2207.06391"@ (2022).

                        [KMY] A. Knutson, E. Miller, and A. Yong. Gröbner Geometry of Vertex
                        Decompositions and of Flagged Tableaux. J. Reine Angew. Math. 630 (2009)
                        1–31.

		        [KR] P. Klein and J. Rajchgot. Geometric Vertex Decomposition and
                        Liaison. Forum of Math, Sigma, 9 (2021) e70:1-23.

                SeeAlso
                        AllowSub
                        CheckCM
                        CheckUnmixed
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
                        [isLexCompatiblyGVD, Verbose]
                Headline
                        checks whether an ideal is <-compatibly geometrically vertex decomposable for a given order
                Usage
                        isLexCompatiblyGVD(I, L)
                Inputs
                        I:Ideal
                        L:List
                Outputs
                        :Boolean
                Description
		 	Text
                                An ideal $I$ is $<$-compatibly geometrically vertex decomposable if
                                there exists a (lexicographic) order $<$ such that $I$ is geometrically vertex
                                decomposable and for every (one-step) geometric vertex decomposition, we
                                pick $y$ to be the most expensive indeterminate remaining in the ideal according
                                to $<$ [KR, Definition 2.11].
                                For the definition of a (one-step) geometric vertex decomposition, see @TO oneStepGVD@.

                                This method returns a Boolean value depending upon whether or not
				the given ideal is $<$-compatibly geometrically vertex decomposable with
				respect to a given ordering lex ordering of the indeterminates.
				Compare this function to the command @TO findLexCompatiblyGVDOrders@ which checks all possible lex
				orders of the variables in order to find at least one $<$-compatibly lex order.

				Below is [KR, Example 2.16], which is an example of an ideal that is not $<$-compatibly geometrically
				vertex decomposable. Any permutation of the variables we give in this example will result in {\tt false}.
			Example
			        R = QQ[x,y,z,w,r,s];
                                I = ideal(y*(z*s - x^2), y*w*r, w*r*(z^2 + z*x + w*r + s^2));
				isLexCompatiblyGVD(I, {x,y,z,w,r,s})
				isLexCompatiblyGVD(I, {s,x,w,y,r,z}, Verbose=>true)
                References
		        [KR] P. Klein and J. Rajchgot. Geometric Vertex Decomposition and
                        Liaison. Forum of Math, Sigma, 9 (2021) e70:1-23.


                SeeAlso
                        CheckCM
                        CheckUnmixed
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
                        :Boolean
                Description
		        Text
			        A function that checks whether an ideal $I \subseteq R$ is unmixed, i.e., the ideal $I$
                                satisfies $\dim(R/I) = \dim(R/P)$ for all associated primes $P \in {\rm Ass}_R(R/I)$.

			        The following example uses  [SM, Example 1.6].
		        Example
			        R = QQ[x_1..x_5];
                                I = ideal(x_1*x_3, x_1*x_4, x_1*x_5, x_2*x_3, x_2*x_4, x_2*x_5);
				isUnmixed I
		References
		        [SM] H. Saremi and A. Mafi. Unmixedness and Arithmetic Properties of
                        Matroidal Ideals. Arch. Math. 114 (2020) 299-304.
                SeeAlso
                        CheckUnmixed
                        isGVD
                        IsIdealUnmixed
                        isLexCompatiblyGVD
                        isWeaklyGVD
///


doc///
        Node
                Key
                        isWeaklyGVD
                        (isWeaklyGVD, Ideal)
                        [isWeaklyGVD, Verbose]
                Headline
                        checks whether an ideal is weakly geometrically vertex decomposable
                Usage
                        isWeaklyGVD I
                Inputs
                        I:Ideal
                Outputs
                        :Boolean
                Description
		        Text
			        This function tests whether an ideal $I \subseteq k[x_1,\ldots,x_n]$ is weakly geometrically vertex decomposable [KR, Definition 4.6].

				See @TO isGVD@ for the definition of the ideals $C_{y,I}$ and $N_{y,I}$ used below. Furthermore, we say that a geometric
				vertex decomposition is {\it degenerate} if $C_{y,I} = \langle 1 \rangle$ or if $\sqrt{C_{y,I}} = \sqrt{N_{y,I}}$.
                                The geometric vertex decomposition is {\it nondegenerate} otherwise.

				An ideal $I \subseteq R = k[x_1, \ldots, x_n]$ is {\it weakly geometrically vertex decomposable} if $I$ is unmixed and

                                (1) $I = \langle 1 \rangle$, or $I$ is generated by a (possibly empty) subset of variables of $R$, or

				(2) (Degenerate Case) for some variable $y = x_j$ of $R$, ${\rm in}_y(I) = C_{y,I} \cap (N_{y,I} + \langle y \rangle)$ is
				a degenerate geometric vertex decomposition and the contraction of $N_{y,I}$ to the ring $k[x_1,\ldots,\hat{y},\ldots,x_n]$
				is weakly geometrically vertex decomposable, or

				(3) (Nondegenerate Case) for some variable $y = x_j$ of $R$,  ${\rm in}_y(I) = C_{y,I} \cap (N_{y,I} + \langle y \rangle)$ is
				a nondegenerate geometric vertex decomposition, the contraction of $C_{y,I}$ to the ring  $k[x_1,\ldots,\hat{y},\ldots,x_n]$
				is weakly geometrically vertex decomposable, and $N_{y,I}$ is radical and Cohen-Macaulay.

		                The following example is [KR, Example 4.10]. It is an example of an ideal that is weakly geometrically
				vertex decomposable, but not geometrically vertex decomposable.
		        Example
                	        R = QQ[x,y,z,w,r,s];
                                I = ideal(y*(z*s - x^2), y*w*r, w*r*(x^2 + s^2 + z^2 + w*r));
				isWeaklyGVD I
				isGVD I

                References
        	        [KR] P. Klein and J. Rajchgot. Geometric Vertex Decomposition and
                        Liaison. Forum of Math, Sigma, 9 (2021) e70:1-23.

                SeeAlso
                        CheckUnmixed
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
                        :Ideal

                Caveat
                        This method is a shortcut to extract the ideal $N_{y,I}$ as computed
                        in @TO oneStepGVD@. That is, to compute $N_{y,I}$, {\tt oneStepGVD} is called in the background.
                        As a result, work is also done in the background to compute $C_{y,I}$ at
                        the same time, and as such, we encourage calling {\tt oneStepGVD}
                        directly if we want both the $C_{y,I}$ and $N_{y,I}$ ideals to avoid
                        performing the same computation twice.
                Description
                        Text
                                Let $y$ be a variable of the polynomial ring $R = k[x_1,\ldots,x_n]$. A monomial ordering $<$ on $R$ is said to be
                                {\it $y$-compatible} if the initial term of $f$ satisfies ${\rm in}_<(f) = {\rm in}_<({\rm in}_y(f))$ for all $f \in R$.
				Here,
				${\rm in}_y(f)$ is the {\it initial $y$-form} of $f$, that is, if $f = \sum_i \alpha_iy^i$ and $\alpha_d \neq 0$
				but $\alpha_t = 0$ for all $t >d$, then ${\rm in}_y(f) = \alpha_d y^d$.

                                Given an ideal $I$ and a $y$-compatible monomial ordering $<$, let $G(I) = \{ g_1,\ldots,g_m\}$ be a Gröbner basis of $I$ with respect to this
                                ordering.  For $i=1,\ldots,m$, write $g_i$ as $g_i = y^{d_i}q_i + r_i$, where $y$ does not divide any term of $q_i$;
                                that is, ${\rm in}_y(g_i) = y^{d_i}q_i$.   Given this setup, the ideal $N_{y,I}$ is given by
                                $$N_{y,I} = \langle q_i ~|~ d_i = 0\rangle$$
                                This functions  takes an ideal $I$ and variable $y$, and returns $N_{y,I}$

                                The ideal $N_{y,I}$ does not depend upon the choice of the Gröbner basis or
                        	a particular $y$-compatible order (see comment after [KR, Definition 2.3]).
				When computing $N_{y,I}$ we use a lexicographical ordering
                        	on $R$ where $y > x_j$ for all $i \neq j$ if $y = x_i$ since this gives us a $y$-compatible order.

                                The ideal $I$ in the example below is the edge ideal of the complete graph $K_4$.
                                For more on edge ideals, see the EdgeIdeals package.

                        Example
                                R = QQ[a,b,c,d];
                                I = ideal(a*b, a*c, a*d, b*c, b*d, c*d); -- edge ideal of a complete graph K_4, a chordal graph
                                NyI(I, b)
                                L = oneStepGVD(I, b);
                                L_2 == NyI(I, b) -- NyI is the second element in the list given by oneStepGVD
		References
		        [KR] P. Klein and J. Rajchgot. Geometric Vertex Decomposition and
                        Liaison. Forum of Math, Sigma, 9 (2021) e70:1-23.

		SeeAlso
                        CheckUnmixed
                        CyI
                        getGVDIdeal
                        oneStepGVD
///


-- need to add that AllowSub and CheckDegenerate are not known to be compatible
doc///
       Node
                Key
                        oneStepGVD
                        (oneStepGVD, Ideal, RingElement)
                        [oneStepGVD, Verbose]
                Headline
                        computes a geometric vertex decomposition
                Usage
                        oneStepGVD(I, y)
                Inputs
                        I:Ideal
                        y:RingElement
                                an indeterminate in the ring
                Outputs
                        :Sequence
                                containing whether the $C_{y,I}$ and $N_{y,I}$ ideals form
                                a valid geometric vertex decomposition, the ideals $C_{y,I}$ and $N_{y,I}$, and if
                                {\tt CheckDegenerate=>true}, whether the one-step decomposition
                                is degenerate or nondegenerate
		Description
			 Text
                                This function computes a geometric vertex decomposition of an ideal based upon work of Knutson,
				Miller, and Yong [KMY, Theorem 2.1].  Geometric vertex decomposition is the key step in the recursive
			        definition of geometrically vertex decomposable ideals.  The function {\tt oneStepGVD} is repeatedly used by @TO isGVD@ to determine
				if an ideal is a geometrically vertex decomposable ideal.

				Let $y$ be a variable of the polynomial ring $R = k[x_1,\ldots,x_n]$. A monomial ordering $<$ on $R$ is said to be
                                {\it $y$-compatible} if the initial term of $f$ satisfies ${\rm in}_<(f) = {\rm in}_<({\rm in}_y(f))$ for all $f \in R$.  Here,
				${\rm in}_y(f)$ is the {\it initial $y$-form} of $f$, that is, if $f = \sum_i \alpha_iy^i$ and $\alpha_d \neq 0$
				but $\alpha_t = 0$ for all $t >d$, then ${\rm in}_y(f) = \alpha_d y^d$.
				We set ${\rm in}_y(I) = \langle {\rm in}_y(f) ~|~ f \in I \rangle$ to be the ideal generated by all the initial $y$-forms in $I$.

                                Given an ideal $I$ and a $y$-compatible monomial ordering $<$, let $G(I) = \{ g_1,\ldots,g_m\}$ be a Gröbner basis of $I$ with respect to this
                                ordering.  For $i=1,\ldots,m$, write $g_i$ as $g_i = y^{d_i}q_i + r_i$, where $y$ does not divide any term of $q_i$;
                                that is, ${\rm in}_y(g_i) = y^{d_i}q_i$.   Given this setup, we define two ideals:
                                $$C_{y,I} = \langle q_1,\ldots,q_m\rangle$$
                                and
                                $$N_{y,I} = \langle q_i ~|~ d_i = 0 \rangle.$$

                                If ${\rm in}_y(I) = C_{y,I} \cap (N_{y,I} + \langle y \rangle),$
                                then we call this decomposition a {\it geometric vertex decomposition of $I$}.

                                Furthermore, we say that a geometric vertex decomposition is {\it degenerate} if
                                $C_{y,I} = \langle 1 \rangle$ or if $\sqrt{C_{y,I}} = \sqrt{N_{y,I}}$.
                                The geometric vertex decomposition is {\it nondegenerate} otherwise.

				For a given variable $y$, the function {\tt oneStepGVD} returns a sequence, where the first element in the sequence is true or false
				depending if the given variable $y$ gives a geometric vertex decomposition of $I$, while the second element is the
				ideal $C_{y,I}$ and the third element in the sequence is the ideal $N_{y,I}$.
                                If {\tt CheckDegenerate=>true}, then there is a fourth element in the output, either "degenerate" or "nondegenerate", corresponding
                                to whether the geometric vertex decomposition is degenerate.

				{\it Note:}  The ideals $C_{y,I}$ and $N_{y,I}$ do not depend upon the choice of the Gröbner basis or
                        	a particular $y$-compatible order (see comment after Definition 2.3 of [KR]).
                        	When computing $C_{y,I}$ and $N_{y,I}$ we use a lexicographical ordering
                        	on $R$ where $y > x_j$ for all $i \neq j$ if $y = x_i$ since this gives us a $y$-compatible order.
			Example
			        R = QQ[a,b,c,d]
                		f = 3*a*b + 4*b*c+ 16*a*c+18*d
                		i = ideal f
                		oneStepGVD(i, a)

                        Text
                                In the example below, the ideal $I$ is the edge ideal of the complete graph $K_4$.  We also check
				if the decomposition is degenerate (see @TO CheckDegenerate@).
                                For more on edge ideals, see the EdgeIdeals package.

                        Example
                                R = QQ[a,b,c,d];
                                i = ideal(a*b, a*c, a*d, b*c, b*d, c*d); -- edge ideal of complete graph K_4, a chordal graph
                                oneStepGVD(i, c, CheckDegenerate=>true)
			Text
			        The example below is the toric ideal of a graph such that the quotient ring is not Cohen-Macaulay.  By [KR, Lemma 2.6], for an ideal $I$
				to have a geometric vertex decomposition with respect to the variable $y$, no term of
				the Gröbner bases can be divided by $y^2$.  In this example, the Gröbner basis of $I$ contains an element with a term
				divisible by $e_1^2$. So $I$ does not have a geometric vertex decomposition with respect to $y = e_1$.
                                For background on toric ideals of graphs, see [CDSRVT, Section 3].

			Example
                	        R = QQ[e_1..e_10];
                		i = ideal(e_1*e_4-e_2*e_3, e_2^2*e_7*e_8*e_9-e_4^2*e_5*e_6*e_10, e_1*e_2*e_7*e_8*e_9-e_3*e_4*e_5*e_6*e_10, e_1^2*e_7*e_8*e_9-e_3^2*e_5*e_6*e_10);
                		mingens gb i
				oneStepGVD(i, e_1)
		References
                        [CDSRVT] M. Cummings, S. Da Silva, J. Rajchgot, and A. Van Tuyl.
                        Geometric Vertex Decomposition and Liaison for Toric Ideals of
                        Graphs. Preprint, @arXiv "2207.06391"@ (2022).

                        [KMY] A. Knutson, E. Miller, and A. Yong. Gröbner Geometry of Vertex
                        Decompositions and of Flagged Tableaux. J. Reine Angew. Math. 630 (2009)
                        1–31.

                        [KR] P. Klein and J. Rajchgot. Geometric Vertex Decomposition and
                        Liaison. Forum of Math, Sigma, 9 (2021) e70:1-23.
		SeeAlso
                        AllowSub
                        CheckDegenerate
                        CheckUnmixed
                        CyI
                        getGVDIdeal
                        isGVD
                        isLexCompatiblyGVD
                        isWeaklyGVD
                        NyI
                        Verbose
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
                        :Ideal
		Description
			 Text
                                Let $y$ be a variable of the polynomial ring $R = k[x_1,\ldots,x_n]$. A monomial ordering $<$ on $R$ is said to be
			       	{\it $y$-compatible} if the initial term of $f$ satisfies ${\rm in}_<(f) = {\rm in}_<({\rm in}_y(f))$ for all $f \in R$.  Here,
			       	${\rm in}_y(f)$ is the {\it initial $y$-form} of $f$, that is, if $f = \sum_i \alpha_iy^i$ and $\alpha_d \neq 0$
			       	but $\alpha_t = 0$ for all $t >d$, then ${\rm in}_y(f) = \alpha_d y^d$.
			       	We set ${\rm in}_y(I) = \langle {\rm in}_y(f) ~|~ f \in I \rangle$ to be the ideal generated by all the initial $y$-forms in $I$

			        This routine computes the ideal of initial $y$-forms ${\rm in}_y(I)$.

                                For more on the definition of initial $y$-forms or their corresponding ideals, see [KMY, Section 2.1]. The following example is
                                [KR, Example 2.16].

                        Example
                                R = QQ[x,y,z,w,r,s]
                                I = ideal(y*(z*s - x^2), y*w*r, w*r*(z^2 + z*x + w*r + s^2))
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


-- add description
doc///
        Node
                Key
                        AllowSub
                        [findOneStepGVD, AllowSub]
                        [isGVD, AllowSub]
                        [oneStepGVD, AllowSub]
                Headline
                        allows for geometric vertex decompositions up to subsitution
                Description
                        Text
                                an optional input, to be implemented for @TO isGVD@, @TO oneStepGVD@, and @TO findOneStepGVD@

                                default value is {\tt false}
                SeeAlso
                        findOneStepGVD
                        isGVD
                        oneStepGVD
///


doc///
        Node
                Key
                        CheckCM
                        [isGVD, CheckCM]
                        [isLexCompatiblyGVD, CheckCM]
                Headline
                        when to perform a Cohen-Macaulay check on the ideal
                Description
                        Text
                                Whether to check that the ideal is geometrically vertex
                                decomposable using the result of [KR, Corollary 4.5] which relates the
                                geometrically vertex decomposable and Cohen-Macaulay properties.
                                Set {\tt CheckCM=>"once"} to perform this check once (default, only for the
                                ideal given in the input), {\tt CheckCM=>"always"} check for
                                the following $C_{y,I}$ and $N_{y,I}$ ideals as well, or
                                {\tt CheckCM=>"never"}.

                References
                        [KR] P. Klein and J. Rajchgot. Geometric Vertex Decomposition and
                        Liaison. Forum of Math, Sigma, 9 (2021) e70:1-23.

                SeeAlso
                        isGVD
                        isLexCompatiblyGVD
///


doc///
        Node
                Key
                        CheckDegenerate
                        [oneStepGVD, CheckDegenerate]
                Headline
                        check whether the geometric vertex decomposition is degenerate
                Description
                        Text
                                A geometric vertex decomposition is degenerate if
                                $\sqrt{C_{y,I}} = \sqrt{N_{y,I}}$ or if $C_{y,I} = \langle 1 \rangle$,
                                and nondegenerate otherwise [KR, Section 2.2].

                                If {\tt CheckDegenerate=>true}, then {\tt oneStepGVD} returns
                                a sequence of length four, where the fourth entry is either
                                {\tt "degenerate"} or {\tt "nondegenerate"}.
                                Otherwise, {\tt oneStepGVD} does not check whether the geometric
                                vertex decomposition is degenerate and the sequence in the output has length three.

                                Note that the degeneracy of a geometric vertex decomposition does not matter
                                with regards to whether an ideal is geometrically vertex decomposable.
                                As a result, @TO isGVD@ does not check this. However, the definition
                                of weakly geometrically vertex decomposable depends the
                                one-step geometric vertex decomposition at each step is degenerate, so
                                @TO isWeaklyGVD@ asks for this check.

                        Example
                                R = QQ[x,y,z]
                                I = ideal(x-y, x-z)
                                oneStepGVD(I, x, CheckDegenerate=>true)

                References
                        [KR] P. Klein and J. Rajchgot. Geometric Vertex Decomposition and
                        Liaison. Forum of Math, Sigma, 9 (2021) e70:1-23.

                SeeAlso
                        isWeaklyGVD
                        oneStepGVD
///


doc///
        Node
                Key
                        CheckUnmixed
                        [CyI, CheckUnmixed]
                        [findLexCompatiblyGVDOrders, CheckUnmixed]
                        [findOneStepGVD, CheckUnmixed]
                        [getGVDIdeal, CheckUnmixed]
                        [isGVD, CheckUnmixed]
                        [isLexCompatiblyGVD, CheckUnmixed]
                        [isWeaklyGVD, CheckUnmixed]
                        [NyI, CheckUnmixed]
                        [oneStepGVD, CheckUnmixed]
                Headline
                        check whether ideals encountered are unmixed
                Description
                        Text

                                If set to {\tt false}, the program never checks whether the ideal $I$ or
                                any $C_{y,I}$ or $N_{y,I}$ ideals are unmixed. Setting {\tt CheckUnmixed=>false}
                                will speed up computations since it is not performing a check of this condition but comes
                                at the cost that not all the necessary conditions are checked.
                                Notice that if {\tt isGVD(I, CheckUnmixed=>false)} returns {\tt false}, then $I$ is
                                conclusively not geometrically vertex decomposable as there is some other condition
                                that is not met.
                                The default value is {\tt true}.

                                If you know that $I$ is unmixed but want to check unmixedness for $C_{y,I}$, $N_{y,I}$,
                                and any later ideals, use @TO IsIdealUnmixed@ instead.

                                The following is not unmixed [SM, Example 1.6] and hence not geometrically vertex
                                decomposable. However, if we disable the unmixedness check and skip the Cohen-Macaulay check,
                                {\tt isGVD} returns true.
                        Example
                                R = QQ[x_1..x_5]
                                I = ideal(x_1*x_3, x_1*x_4, x_1*x_5, x_2*x_3, x_2*x_4, x_2*x_5)
                                isUnmixed I
                                isGVD(I, CheckCM=>"never", CheckUnmixed=>false)

                Caveat
                        As in the above example, if you set {\tt CheckUnmixed=>false} and you do not already know
                        that both $I$ is unmixed and all later $C_{y,I}$ and $N_{y,I}$ ideals are unmixed, then the
                        output of @TO isGVD@ or any other GVD method cannot definitely conclude that $I$ is geometrically
                        vertex decomposable, as not all of conditions in the definition were checked.

                References
                        [SM] H. Saremi and A. Mafi. Unmixedness and Arithmetic Properties of
                        Matroidal Ideals. Arch. Math. 114 (2020) 299–304.


                SeeAlso
                        CyI
                        findLexCompatiblyGVDOrders
                        findOneStepGVD
                        getGVDIdeal
                        isGVD
                        IsIdealUnmixed
                        isLexCompatiblyGVD
                        isUnmixed
                        isWeaklyGVD
                        NyI
                        oneStepGVD
///


doc///
        Node
                Key
                        IsIdealHomogeneous
                        [isGVD, IsIdealHomogeneous]
                        [isLexCompatiblyGVD, IsIdealHomogeneous]
                Headline
                        specify whether an ideal is homogeneous
                Description
                        Text
                                Whether the input ideal is homogeneous, if known.
                                The value of this input is only checked if {\tt CheckCM=>true}.
                SeeAlso
                        CheckCM
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
                        specify whether an ideal is unmixed
                Description
                        Text
                                Specify {\tt IsIdealUnmixed=>true} if it is known {\em a priori}
                                that an ideal is unmixed. In this case, the program will not
                                check whether the given ideal $I$ is unmixed -- it will assume
                                that it is unmixed -- but it will check whether $C_{y,I}$ and
                                $N_{y,I}$ are unmixed, as well as any ideals defined from further
                                degenerations.
                                The default value is {\tt false} and in this case, the unmixedness
                                property will be checked for $I$ and all later ideals.

                                To always skip the unmixedness check (perhaps you know that
                                every ideal you will encounter through repeated geometric vertex decompositions
                                will always be unmixed), use @TO CheckUnmixed@.

                SeeAlso
                        CheckUnmixed
                        isGVD
                        isLexCompatiblyGVD
                        isUnmixed
                        isWeaklyGVD
///


doc///
        Node
                Key
                        OnlyDegenerate
                        [findOneStepGVD, OnlyDegenerate]
                Headline
                        restrict to degenerate geometric vertex decompositions
                Description
                        Text
                                Set to {\tt true} to restrict the output of @TO findOneStepGVD@ to return only
                                the indeterminates for which their geometric vertex decomposition is degenerate.
                                Default value {\tt false}.
                SeeAlso
                        findOneStepGVD
                        OnlyNondegenerate
///


doc///
        Node
                Key
                        OnlyNondegenerate
                        [findOneStepGVD, OnlyNondegenerate]
                Headline
                        restrict to nondegenerate geometric vertex decompositions
                Description
                        Text
                                Set to {\tt true} to restrict the output of @TO findOneStepGVD@ to return only
                                the indeterminates for which their geometric vertex decomposition is nondegenerate.
                                Default value {\tt false}.
                SeeAlso
                        findOneStepGVD
                        OnlyDegenerate
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
C = CyI(I,y);
assert( CyI(I, y) == ideal(x*z*w*r+z^2*w*r+w^2*r^2+w*r*s^2,w*r,x^2-z*s) )
///


TEST///  -- [KR, Example 4.10]
R = QQ[x..z,w,r,s];
I = ideal( y*(z*s - x^2), y*w*r, w*r*(x^2 + s^2 + z^2 + w*r) );
assert( CyI(I, y) == ideal(z*s-x^2, w*r) )
///


--------------------------------------------------------------------------------
-- Test findLexCompatiblyGVDOrders
--------------------------------------------------------------------------------


TEST///
R = QQ[x,y];
I = ideal(x^2 - y^2);
assert(findLexCompatiblyGVDOrders I == {})
///


TEST///
R = QQ[x..z];
I = ideal(x-y, x-z);
assert( findLexCompatiblyGVDOrders I == {{x, y, z}, {x, z, y}, {y, x, z}, {y, z, x}, {z, x, y}, {z, y, x}} )
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


TEST///  -- Toric ideal of the complete bipartite graph K_{3,2}; GVD by [CDSRVT, Theorem 5.8]
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


TEST///  -- Hessenberg patch ideal corresponding to the $w_0$ chart and Hessenberg function h=(2,3,4,5,6,6), GVD by [DSH, Corollary 5.13]
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
R = QQ[x,y];
I = ideal(x^2 - y^2);
assert(not isLexCompatiblyGVD(I, {x,y}))
///


TEST///
R = QQ[x..z];
I = ideal(x-y,x-z);
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


TEST///  -- Unmixed by [DSH, Corollary 5.13]
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
assert( oneStepGVD(I, y, CheckDegenerate=>true) == (true, ideal(x*z*w*r+z^2*w*r+w^2*r^2+w*r*s^2,w*r,x^2-z*s), ideal(x*z*w*r+z^2*w*r+w^2*r^2+w*r*s^2), "nondegenerate") )
///


TEST///  -- [KR, Example 4.10]
R = QQ[x..z,w,r,s];
I = ideal( y*(z*s - x^2), y*w*r, w*r*(x^2 + s^2 + z^2 + w*r) );
assert( oneStepGVD(I, y, CheckDegenerate=>true) == (true, ideal(z*s-x^2, w*r), ideal(x^2*w*r+w*r*s^2+z^2*w*r+w^2*r^2), "nondegenerate") )
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
