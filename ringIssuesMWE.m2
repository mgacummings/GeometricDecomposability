newPackage(
        "ringIssuesMWE",
        Version => "1.0",
        Date => "July 14, 2022",
        Headline => "An example of the issues of working with rings"
        )

export {
        "changeUsersRing"
        };

changeUsersRing = method(TypicalValue => Ideal)
changeUsersRing(Ideal) := I -> (
        S := (coefficientRing ring I)[support I];
        return I;
        )

beginDocumentation()

doc///
        Node
                Key
                        ringIssuesMWE
                Headline
                        an example of the issues of working with rings
                Description
                        Text
                                Rings defined locally within methods change the user's ring, as seen in
                                @TO changeUsersRing@.
                Subnodes
                        changeUsersRing
///

doc///
        Node
                Key
                        changeUsersRing
                        (changeUsersRing, Ideal)
                Headline
                        changes the ring that the user is working with
                Usage
                        changeUsersRing I
                Inputs
                        I:Ideal
                Description
                        Text
                                This function takes an ideal and returns it, while changing the ring
                                in the background.
///
--
