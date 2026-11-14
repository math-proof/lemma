-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_DoubleComplex.lean: instance decls only.
-- The E₂I / E₂II AddCommGroup and Module instances cannot live here: they need
-- `Def.AlgebraicGeometry_DoubleComplex`, but Def and Structure already import this
-- module, which made a build cycle. Host those instances next to the Def abbrevs
-- (quotient instances often infer) rather than importing Def from Instance.
import Mathlib

set_option autoImplicit false
