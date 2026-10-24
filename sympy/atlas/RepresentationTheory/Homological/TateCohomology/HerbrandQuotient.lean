/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RepresentationTheory/Homological/TateCohomology/HerbrandQuotient.lean -/

import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.SetTheory.Cardinal.Finite

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

universe u

namespace TateCohomology

open CategoryTheory

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- Cardinality of degree-`n` Tate cohomology of `M`. -/
noncomputable def tateCohomologyCard (M : Rep R G) (n : ℤ) : Cardinal :=
  Cardinal.mk ↥(tateCohomology M n)

/-- Cardinality of degree-`n` Tate homology, via `H_hat_n = H_hat^(-n-1)`. -/
noncomputable def tateHomologyCard (M : Rep R G) (n : ℤ) : Cardinal :=
  tateCohomologyCard M (-n - 1)

/-- Degree-zero Tate homology is cohomological degree `-1`. -/
@[simp] theorem tateHomologyCard_zero (M : Rep R G) :
    tateHomologyCard M 0 = tateCohomologyCard M (-1) := rfl

/-- Finiteness of the two degrees entering the Herbrand quotient. -/
def HerbrandFinite (M : Rep R G) : Prop :=
  Finite ↥(tateCohomology M 0) ∧ Finite ↥(tateCohomology M (-1))

/-- Herbrand quotient `h^0 / h_0` in `ℚ`, gated on finiteness. -/
noncomputable def herbrandQuotient (M : Rep R G) (h : HerbrandFinite M) : ℚ :=
  haveI := h.1
  haveI := h.2
  (Nat.card ↥(tateCohomology M 0) : ℚ) / Nat.card ↥(tateCohomology M (-1))
end TateCohomology
