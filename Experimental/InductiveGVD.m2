newPackage(
        "InductiveGVD",
        Headline => "a sample package"
)

export {
        "isGVD"
}

-* Helper code section *-

isGeneratedByIndeterminates = method(TypicalValue => Boolean)
isGeneratedByIndeterminates(Ideal) := I -> (
        R := ring I;
        indeterminates := gens R;
        gensI := first entries gens I;
        return isSubset(delete(0, gensI), indeterminates);
        )


isUnmixed = method(TypicalValue => Boolean)
isUnmixed(Ideal) := I -> (
        R := ring I;
        D := primaryDecomposition I;
        d := apply(D, i -> dim(R/i));
        return all(apply(d, i -> (i == d_0)), i -> i);  -- list contains only true values
        )


-- [KMY, Theorem 2.1]
oneStepGVD = method(TypicalValue => Sequence, Options => {CheckDegenerate => false, CheckUnmixed => true, Verbose => false})
oneStepGVD(Ideal, RingElement) := opts -> (I, y) -> (

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

-* Code section *-

isGVD = method(TypicalValue => Boolean)
foo(Ideal) := I -> (
        if (I == 0 or I == 1 or isGeneratedByIndeterminates I) then (return true);
        if not (isUnmixed I) then (return false);
        
)

-* Documentation section *-
beginDocumentation()

doc ///
        Key
                InductiveGVD
        Subnodes
                isGVD
///

doc ///
        Key
                isGVD
                (isGVD, Ideal)
///

end