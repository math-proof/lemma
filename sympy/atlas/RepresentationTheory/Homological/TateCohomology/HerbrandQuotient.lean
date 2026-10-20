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

/-- Under finiteness, the cardinal is the cast of `Nat.card`. -/
theorem tateCohomologyCard_eq_natCast (M : Rep R G) (n : ℤ)
    [Finite ↥(tateCohomology M n)] :
    tateCohomologyCard M n = Nat.card ↥(tateCohomology M n) :=
  Nat.cast_card.symm

/-- Finiteness of the two degrees entering the Herbrand quotient. -/
def HerbrandFinite (M : Rep R G) : Prop :=
  Finite ↥(tateCohomology M 0) ∧ Finite ↥(tateCohomology M (-1))

/-- Herbrand quotient `h^0 / h_0` in `ℚ`, gated on finiteness. -/
noncomputable def herbrandQuotient (M : Rep R G) (h : HerbrandFinite M) : ℚ :=
  haveI := h.1
  haveI := h.2
  (Nat.card ↥(tateCohomology M 0) : ℚ) / Nat.card ↥(tateCohomology M (-1))

/-- Unfolding of the Herbrand quotient as a ratio of `Nat.card`s. -/
theorem herbrandQuotient_eq (M : Rep R G) (h : HerbrandFinite M) :
    herbrandQuotient M h = (Nat.card ↥(tateCohomology M 0) : ℚ) /
      Nat.card ↥(tateCohomology M (-1)) := rfl

/-- The denominator of the Herbrand quotient is positive. -/
theorem herbrandQuotient_den_pos (M : Rep R G) (h : HerbrandFinite M) :
    0 < Nat.card ↥(tateCohomology M (-1)) := by
  have := h.2
  exact Nat.card_pos

/-- The denominator of the Herbrand quotient is nonzero. -/
theorem herbrandQuotient_den_ne_zero (M : Rep R G) (h : HerbrandFinite M) :
    Nat.card ↥(tateCohomology M (-1)) ≠ 0 :=
  ne_of_gt (herbrandQuotient_den_pos M h)

/-- The Herbrand quotient is positive. -/
theorem herbrandQuotient_pos (M : Rep R G) (h : HerbrandFinite M) :
    0 < herbrandQuotient M h := by
  have := h.1
  have := h.2
  rw [herbrandQuotient_eq]
  exact div_pos (Nat.cast_pos.mpr Nat.card_pos) (Nat.cast_pos.mpr Nat.card_pos)

/-- Invariance under carrier equivalences in degrees `0` and `-1`. -/
theorem herbrandQuotient_congr {M N : Rep R G} {hM : HerbrandFinite M}
    {hN : HerbrandFinite N}
    (e₀ : ↥(tateCohomology M 0) ≃ ↥(tateCohomology N 0))
    (e₁ : ↥(tateCohomology M (-1)) ≃ ↥(tateCohomology N (-1))) :
    herbrandQuotient M hM = herbrandQuotient N hN := by
  rw [herbrandQuotient_eq, herbrandQuotient_eq, Nat.card_congr e₀,
    Nat.card_congr e₁]

end TateCohomology
