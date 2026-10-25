/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RepresentationTheory/Homological/TateCohomology/HerbrandQuotient.lean -/

import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Def.RepresentationTheory.Homological.TateCohomology.HerbrandQuotient
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

/-- Degree-zero Tate homology is cohomological degree `-1`. -/
@[simp] theorem tateHomologyCard_zero (M : Rep R G) :
    tateHomologyCard M 0 = tateCohomologyCard M (-1) := rfl

end TateCohomology
