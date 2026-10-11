import Mathlib.RingTheory.Nullstellensatz
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Defined-over for affine algebraic sets

For a field `k`, the ideal of polynomials over `k` vanishing on
`Z ⊆ AlgebraicClosure k ^ n` is the comap of the Mathlib vanishing ideal
over the algebraic closure. A set is defined over `k` when its vanishing
ideal is extended from that comap ideal.
-/

noncomputable section

variable {k : Type*} [Field k]

namespace MvPolynomial

/-- The ideal `I_k(Z) ⊆ k[X]` of polynomials over `k` vanishing on `Z`,
obtained by pulling back the vanishing ideal over the algebraic closure. -/
noncomputable def idealOverK {n : ℕ} (Z : Set (Fin n → AlgebraicClosure k)) :
    Ideal (MvPolynomial (Fin n) k) :=
  Ideal.comap (MvPolynomial.map (algebraMap k (AlgebraicClosure k)))
    (MvPolynomial.vanishingIdeal (AlgebraicClosure k) Z)

/-- `f ∈ I_k(Z)` iff its image in `AlgebraicClosure k[X]` vanishes on `Z`. -/
theorem mem_idealOverK_iff {n : ℕ} {Z : Set (Fin n → AlgebraicClosure k)}
    {f : MvPolynomial (Fin n) k} :
    f ∈ idealOverK Z ↔
      MvPolynomial.map (algebraMap k (AlgebraicClosure k)) f ∈
        MvPolynomial.vanishingIdeal (AlgebraicClosure k) Z := by
  rfl

/-- `Z ⊆ AlgebraicClosure k ^ n` is defined over `k` if its vanishing ideal is
the extension of `I_k(Z)`. -/
def IsDefinedOver {n : ℕ} (Z : Set (Fin n → AlgebraicClosure k)) : Prop :=
  MvPolynomial.vanishingIdeal (AlgebraicClosure k) Z =
    Ideal.map (MvPolynomial.map (algebraMap k (AlgebraicClosure k)))
      (idealOverK Z)

/-- Unfolding of `IsDefinedOver` as an equality of ideals. -/
theorem isDefinedOver_iff {n : ℕ} (Z : Set (Fin n → AlgebraicClosure k)) :
    IsDefinedOver Z ↔
      MvPolynomial.vanishingIdeal (AlgebraicClosure k) Z =
        Ideal.map (MvPolynomial.map (algebraMap k (AlgebraicClosure k)))
          (idealOverK Z) := by
  rfl

/-- Membership in `I_k(Z)` implies vanishing of the extended polynomial. -/
theorem eval_of_mem_idealOverK {n : ℕ} {Z : Set (Fin n → AlgebraicClosure k)}
    {f : MvPolynomial (Fin n) k} (hf : f ∈ idealOverK Z)
    {P : Fin n → AlgebraicClosure k} (hP : P ∈ Z) :
    MvPolynomial.eval P
      (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) f) = 0 := by
  have h := (mem_idealOverK_iff.mp hf)
  rw [MvPolynomial.mem_vanishingIdeal_iff] at h
  exact h P hP

/-- The ideal over `k` of the empty set is the whole ring. -/
theorem idealOverK_empty (n : ℕ) :
    idealOverK (∅ : Set (Fin n → AlgebraicClosure k)) = ⊤ := by
  rw [idealOverK, MvPolynomial.vanishingIdeal_empty, Ideal.comap_top]

/-- `I_k` is antitone in the set. -/
theorem idealOverK_anti_mono {n : ℕ} {Z₁ Z₂ : Set (Fin n → AlgebraicClosure k)}
    (h : Z₁ ⊆ Z₂) : idealOverK Z₂ ≤ idealOverK Z₁ :=
  Ideal.comap_mono (MvPolynomial.vanishingIdeal_anti_mono h)

end MvPolynomial

end
