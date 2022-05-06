-- -*- coding: utf-8 -*-

newPackage(
  "GeometricVertexDecomposition",
  Version => "0.0",
  Date => "April 6, 2022",
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
  Keywords => {"Algebraic Geometry"},  --keywords from the headings here: http://www2.macaulay2.com/Macaulay2/doc/Macaulay2-1.17/share/doc/Macaulay2/Macaulay2Doc/html/_packages_spprovided_spwith_sp__Macaulay2.html
  PackageImports => {"PrimaryDecomposition", "Depth"},  -- I don't think these need to be imported for the user? Hence PackageImports and not PackageExports
  HomePage => ""  -- homepage for the package, if one exists, otherwise remove
  )

export {  -- list of functions which will be visible to the user

  }

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--
-- FUNCTIONS
--
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------






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



end--
