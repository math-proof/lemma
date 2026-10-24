/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ConductorResidue.lean -/

import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Residue rings at primes avoiding a denominator-clearing ideal

Let `O → B` be a commutative-ring algebra, `q` a maximal ideal of `B`, and `c` an
ideal of `B` not contained in `q`. Suppose elements of `c` clear arbitrary elements
of `B` back into the image of `O`:

  `hclear : ∀ x ∈ c, ∀ b : B, ∃ o : O, algebraMap O B o = x * b`.

Then the canonical map induces an isomorphism
`O ⧸ q.comap (algebraMap O B) ≃+* B ⧸ q`, with consequences for `Nat.card` and
`Submodule.cardQuot`.

This is the prime-local slice of ATLAS `NumberTheoryI` Proposition 6.32, stated for
an arbitrary commutative-ring algebra rather than for orders in a number field. It
generalizes the monogenic case `Ideal.quotAdjoinEquivQuotMap`, where the
denominator-clearing ideal is the conductor of a single adjoined element.
-/

noncomputable section

namespace Ideal

variable {O B : Type*} [CommRing O] [CommRing B] [Algebra O B]
variable (q : Ideal B) [q.IsMaximal] (c : Ideal B)

/-- Canonical residue-ring equivalence at a maximal ideal `q` coprime to a
denominator-clearing ideal `c`: the map induced by `algebraMap O B` is an
isomorphism `O ⧸ q.comap (algebraMap O B) ≃+* B ⧸ q`. -/
def quotient_coprime_residue_equiv (hc : ¬ c ≤ q)
    (hclear : ∀ x ∈ c, ∀ b : B, ∃ o : O, algebraMap O B o = x * b) :
    O ⧸ q.comap (algebraMap O B) ≃+* B ⧸ q := by
  refine RingEquiv.ofBijective (Ideal.quotientMap q (algebraMap O B) le_rfl)
    ⟨Ideal.quotientMap_injective, ?_⟩
  obtain ⟨s, hs_mem, hs_notin⟩ := SetLike.not_le_iff_exists.mp hc
  obtain ⟨a₀, q₀, hq₀, ha₀⟩ := (inferInstance : q.IsMaximal).exists_inv hs_notin
  intro y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨o, ho⟩ := hclear s hs_mem (b * a₀)
  refine ⟨Ideal.Quotient.mk _ o, ?_⟩
  simp only [Ideal.quotientMap_mk]
  rw [Ideal.Quotient.eq]
  have h1 : s * a₀ = 1 - q₀ := by linear_combination ha₀
  have hkey : algebraMap O B o - b = -(b * q₀) := by
    calc algebraMap O B o - b = s * (b * a₀) - b := by rw [ho]
      _ = b * (s * a₀) - b := by ring
      _ = b * (1 - q₀) - b := by rw [h1]
      _ = -(b * q₀) := by ring
  rw [hkey]
  exact q.neg_mem (q.mul_mem_left b hq₀)
end Ideal
