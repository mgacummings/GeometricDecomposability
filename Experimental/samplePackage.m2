newPackage(
        "samplePackage",
        Headline => "a sample package"
)

export {
        "foo"
}

-* Code section *-

foo = method(TypicalValue => Boolean, Options => {Verbose => false})
foo(Boolean) := opts -> b -> (
        return not b;
)

-* Documentation section *-
beginDocumentation()

doc ///
        Key
                samplePackage
        Subnodes
                foo
///

doc ///
        Key
                foo
                (foo, Boolean)
                [foo, Verbose]
        SeeAlso
                Verbose
///

end