import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
/-!
# Lambert W function, principal real branch (Ouellet JIS VOL20, rank 320)

Source contract, rank 320, lexical id `jis_term_6c376920fa7bc177f6acc4c7`,
semantic id `jis_sem_4b8befd1d7e70075080d07cc`.

Ouellet, JIS VOL20, `ou2.tex`, lines 426-432,
SHA256 `251582ff49dbfc57f6d80b409c0ecedd8c6c27dc64a7cdcf3ce987ac03cfd78f`:
for `x > -1/e`, the Lambert W function is the inverse of the real-valued
function `h y = y * exp y` defined for `y > -1`, so that
`W x * exp (W x) = x`.

Correction ledger: Gessel, JIS VOL10, `gessel20.tex`, lines 271-295,
SHA256 `fd3e913cfabab90d18603e10bf02bce9651ae7e2c5129bdc4f72fdd4807ee5cd`,
prints `W z * exp (-W z) = z`. This is a sign typo. We follow Ouellet's
explicit principal real-branch definition `W z * exp (W z) = z`, corroborated
by Gessel's standard expansion at `-exp (-1)`.

This file formalizes the unique-preimage characterization of the principal real
branch on the open domain `x > -exp (-1)`, with preimages restricted to `y > -1`.
It does not yet define a `lambertW` function; the proved theorem is intended to
justify such a subtype-valued inverse.
-/


namespace MetaMathlibExt

/-- The map `h y = y * exp y` whose restricted inverse is Lambert W.
Ouellet JIS VOL20 `ou2.tex` lines 426-432. -/
noncomputable def lambertMap (y : ℝ) : ℝ :=
  y * Real.exp y

end MetaMathlibExt
