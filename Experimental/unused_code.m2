--------------------------------------------------------------------------------

-*
-- [KMY, Theorem 2.1]
OLDoneStepGVD = method(
        TypicalValue => Sequence, 
        Options => {
                AllowSub => false,  -- not yet implemented
                CheckDegenerate => false, 
                CheckUnmixed => true, 
                Verbose => false
                }
        )
OLDoneStepGVD(Ideal, RingElement) := opts -> (I, y) -> (

        -- set up the rings
        indeterminates := switch(0, index y, gens ring y);
        remainingIndets := drop(gens ring y, {index y, index y});
        cr := coefficientRing ring I;

        givenRing := ring I;
        lexRing := (cr) monoid([indeterminates, MonomialOrder=>Lex]);
        contractedRing := (cr) monoid([remainingIndets]);

        -- pull everything into a lex ring
        I1 := sub(I, lexRing);
        y1 := sub(y, lexRing);
        inyForm := sub(yInit(I1, y1), lexRing);
        G := first entries gens gb I1;

        -- get N_{y,I}
        gensN := delete(0, apply(G, g -> isInN(g, y1)));
        NyI := ideal(gensN);

        -- get C_{y, I} and determine whether the GB is square-free in y
        gensC := delete(true, flatten(apply(G, g -> isInC(g, y1))));
        squarefree := (number(gensC, i -> (i === false)) == 0);  -- square-free is true iff number of `false` in gensC is 0
        CyI := ideal(delete(false, gensC));

        -- [KR, Lemma 2.6]
        if not squarefree then (
                printIf(opts.Verbose, "Warning: Gröbner basis not square-free in " | toString y);
                return (false, sub(CyI, givenRing), sub(NyI, givenRing));
                );

        -- check that the intersection holds
        -- sub CyI, NyI into lexRing in case either is zero or unit ideal
        validOneStep := ( intersect( sub(CyI, lexRing), sub(NyI, lexRing) + ideal(y1) ) == inyForm );

        C := sub(CyI, givenRing);
        N := sub(NyI, givenRing);

        if not validOneStep then (
                printIf(opts.Verbose, "Warning: not a valid geometric vertex decomposition");
                return (false, C, N);
                );

        if opts.CheckUnmixed then (
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
                        return (false, C, N);
                        );
                );

        if opts.CheckDegenerate then (
                -- degenerate if C == 1 or radical C == radical N
                if C == 1 then return (true, C, N, "degenerate");

                radC := radical(C, Unmixed=>true);
                radN := radical(N, Unmixed=>true);
                if (radC == radN) then return (true, C, N, "degenerate");

                -- if we are here, we are nondegenerate
                return (true, C, N, "nondegenerate");
                );
        return (true, C, N);
        )

--------------------------------------------------------------------------------

oneStepSubGVD = method(
        TypicalValue => Sequence, 
        Options => {
                CheckUnmixed => true, 
                Verbose => false
                }
        )
oneStepSubGVD(Ideal, RingElement) := opts -> (I, y) -> (

        -- set up the rings
        indeterminates := switch(0, index y, gens ring y);
        remainingIndets := drop(gens ring y, {index y, index y});
        cr := coefficientRing ring I;

        givenRing := ring I;
        lexRing := (cr) monoid([indeterminates, MonomialOrder=>Lex]);
        contractedRing := (cr) monoid([remainingIndets]);

        -- pull everthing into the new rings
        J := sub(I, lexRing);
        z := sub(y, lexRing);

        G := first entries gens gb J;
        gbTerms := flatten apply(G, f -> terms f);
        yDegrees := unique apply(gbTerms, m -> degree(z, m));

        yMaxDegree := max yDegrees;
        yOtherDegrees := delete(0, delete(yMaxDegree, yDegrees));  -- all degrees of y in the GB that are not 0 and not the highest degree

        noOtherYDegrees := (#yOtherDegrees == 0);

        -- get N_{y,I}
        gensN := delete(0, apply(G, g -> isInN(g, z)));
        NyI := ideal(gensN);

        -- get C_{y, I}
        gensC := delete(true, flatten(apply(G, g -> isInC(g, z))));
        CyI := ideal(delete(false, gensC));

        C := sub(CyI, contractedRing);
        N := sub(NyI, contractedRing);

        if opts.CheckUnmixed then (
                -- check unmixedness of both CyI and NyI
                isUnmixedC := isUnmixed C;
                isUnmixedN := isUnmixed N;

                bothUnmixed := (isUnmixedC and isUnmixedN);

                if not isUnmixedC then (
                        printIf(opts.Verbose, "Warning: CyI is not unmixed");
                        );
                if not isUnmixedN then (
                        printIf(opts.Verbose, "Warning: NyI is not unmixed");
                        );

                canSub := (noOtherYDegrees and bothUnmixed);
                return (canSub, C, N);
        );
        
        return (noOtherYDegrees, C, N);
        )
*-

--------------------------------------------------------------------------------

-*
subGVD = method(TypicalValue => RingElement)
subGVD(RingElement, RingElement, ZZ) := (f, y, d) -> (
        
        if not (ring f === ring y) then (
                error("inputs do not belong to the same ring");
                return;
                );

        givenRing := ring f;
        cr := coefficientRing ring f;
        givenIndets := gens ring f;
        yIndex := index y;  -- the index of y in ```gens ring y```

        oldIndetsNewOrder := switch(0, index y, givenIndets);  -- y is the 0th entry of this list
        otherOldIndets := drop(oldIndetsNewOrder, {0, 0});

        tempRing := (cr) monoid([oldIndetsNewOrder]);

        I := sub(ideal f, tempRing);
        z := sub(y, tempRing);
        otherOldIndetsNewRing := apply(otherOldIndets, x -> sub(x, tempRing));

        -- ring maps
        F := map(tempRing, tempRing, prepend(z^d, otherOldIndetsNewRing));
        identityMap := map(tempRing, tempRing, prepend(z, otherOldIndetsNewRing));

        J := preimage(F, I);
        I1 := identityMap J;

        return sub(first flatten entries gens I1, givenRing);
        )
*-

-*
-- more to fill in here
doc///
        Node
                Key
                        oneStepSubGVD
                        (oneStepSubGVD, Ideal, RingElement)
                        [oneStepSubGVD, Verbose]
                Headline
                        computes a geometric vertex decomposition after substitution
                Usage
                        oneStepSubGVD(I, y)
                Inputs
                        I:Ideal
                        y:RingElement
                                an indeterminate in the ring
                Outputs
                        :Sequence
                                containing whether the $C_{y,I}$ and $N_{y,I}$ ideals form
                                a valid geometric vertex decomposition and the ideals $C_{y,I}$ and $N_{y,I}$
                Description
                        Text
                                To be filled in...
                References
                        None...
                SeeAlso
                        CheckUnmixed
                        isGVDuptoSub
                        Verbose
///
*-

-*
-- more to fill in here
doc///
        Node
                Key
                        subGVD
                        (subGVD, RingElement, RingElement, ZZ)
                Headline
                        
///
*-