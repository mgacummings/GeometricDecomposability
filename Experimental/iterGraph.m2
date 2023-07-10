loadPackage "NautyGraphs";
installPackage "GeometricDecomposabilityExperimental";

-- slight modification from the version included in the Quasidegrees package,
-- but can handle the case where there are no even cycles in the graph
toricIdeal = (A, R) -> (
        m := product gens R;
        return saturate(sub(toBinomial(transpose(syz(A)),R),R),m);
)

-- ring with 28 indeterminates (for the up to 28 edges we will see)
R = QQ[e_1..e_28];

-- iterate of number of vertices
for n from 4 to 8 do (
        GList := generateGraphs(n, OnlyConnected=>true);

        run "date";
        print("There are " | #GList | " finite, simple, and connected graphs on " | n | " vertices,");

        nonZeroList := select( apply(GList, g -> toricIdeal(incidenceMatrix stringToGraph g, R)), I -> I != 0 );
        numNonzero := #nonZeroList;
        print(numNonzero | " of which are nonzero, and");

        notSubGVD := select(nonZeroList, I -> not isGVD(I, AllowSub=>true));
        numNotSubGVD := #notSubGVD;
        numSubGVD := numNonzero - numNotSubGVD;
        print(numSubGVD | " of which are GVD up to substitution");
        print("");
)