/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RepresentationTheory/Homological/TateCohomology/HerbrandQuotient.lean -/

import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.SetTheory.Cardinal.Finite
universe u

/-!
# Herbrand quotient of Tate cohomology

For a finite group `G` and `M : Rep R G`, `h^n` is the cardinality of Tate
cohomology `tateCohomology M n`, and `h_n` the cardinality of Tate homology,
defined from cohomology by `H_hat_n = H_hat^(-n-1)`. When degrees `0` and
`-1` are finite, the Herbrand quotient is `h = h^0 / h_0` in `ℚ`.

The classical statement asks for finite *cyclic* `G`, but Mathlib's
`tateCohomology` (and hence everything here) needs only `[Group G]`
`[Fintype G]`; no cyclicity hypothesis is used.
-/


namespace TateCohomology

open CategoryTheory

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- Cardinality of degree-`n` Tate cohomology of `M`. -/
noncomputable def tateCohomologyCard (M : Rep R G) (n : ℤ) : Cardinal :=
  Cardinal.mk ↥(tateCohomology M n)

/-- Cardinality of degree-`n` Tate homology, via `H_hat_n = H_hat^(-n-1)`. -/
noncomputable def tateHomologyCard (M : Rep R G) (n : ℤ) : Cardinal :=
  tateCohomologyCard M (-n - 1)

end TateCohomology
