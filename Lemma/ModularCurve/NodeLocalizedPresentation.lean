import Mathlib
import Lemma.ModularCurve.NodeLocalized
import Abbrev.ModularCurve_NodeLocalizedPresentation

set_option autoImplicit false

noncomputable section

namespace ModularCurve
namespace NodeLocalized

open MvPolynomial

section Presentation

variable (N : ℕ) [NeZero N] {L : Type*} [Field L] (A : Subring L) {k : Type*} [Field k] (red : A →+* k) (a b : k)

def modularEvalAt : MvPolynomial (Fin 2) A →+* modularLocalizedAtPoint N A red a b :=
  (modularEval N A).codRestrict _ (modularEval_mem_modularLocalizedAtPoint N A red a b)

@[simp] theorem coe_modularEvalAt (p : MvPolynomial (Fin 2) A) :
    (modularEvalAt N A red a b p : LaurentSeries L) = modularEval N A p := rfl

theorem evalRange_le : evalRange N A ≤ modularLocalizedAtPoint N A red a b := by
  rintro _ ⟨p, rfl⟩
  exact modularEval_mem_modularLocalizedAtPoint N A red a b p


theorem algebraMap_evalRange_coe (y : evalRange N A) :
    ((algebraMap (evalRange N A) (modularLocalizedAtPoint N A red a b) y : modularLocalizedAtPoint N A red a b) :
      LaurentSeries L) = y := rfl

theorem algebraMap_evalRange_rangeRestrict (p : MvPolynomial (Fin 2) A) :
    algebraMap (evalRange N A) (modularLocalizedAtPoint N A red a b) ((modularEval N A).rangeRestrict p)
      = modularEvalAt N A red a b p := rfl

def nodeDenominators : Submonoid (evalRange N A) where
  carrier := {y | ∃ s : MvPolynomial (Fin 2) A, pointEval A red a b s ≠ 0 ∧ (modularEval N A).rangeRestrict s = y}
  one_mem' := ⟨1, by rw [map_one]; exact one_ne_zero, by rw [map_one]⟩
  mul_mem' := by
    rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    exact ⟨s * t, by rw [map_mul]; exact mul_ne_zero hs ht, by rw [map_mul]⟩

theorem rangeRestrict_mem_nodeDenominators {s : MvPolynomial (Fin 2) A} (hs : pointEval A red a b s ≠ 0) :
    (modularEval N A).rangeRestrict s ∈ nodeDenominators N A red a b :=
  ⟨s, hs, rfl⟩

theorem mem_nodeDenominators_iff (y : evalRange N A) :
    y ∈ nodeDenominators N A red a b ↔ ∃ s : MvPolynomial (Fin 2) A, pointEval A red a b s ≠ 0 ∧ modularEval N A s = y := by
  constructor
  · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, h⟩; exact ⟨s, hs, Subtype.ext h⟩

section KerLE

variable [hker : Fact (RingHom.ker (modularEval N A) ≤ RingHom.ker (pointEval A red a b))]

theorem modularEval_ne_zero_of_pointEval_ne_zero {s : MvPolynomial (Fin 2) A} (hs : pointEval A red a b s ≠ 0) :
    modularEval N A s ≠ 0 := fun h => hs (hker.out ((RingHom.mem_ker).mpr h))

theorem isUnit_modularEvalAt {s : MvPolynomial (Fin 2) A} (hs : pointEval A red a b s ≠ 0) :
    IsUnit (modularEvalAt N A red a b s) := by
  have hs0 := modularEval_ne_zero_of_pointEval_ne_zero N A red a b hs
  refine isUnit_iff_exists_inv.mpr ⟨⟨(modularEval N A s)⁻¹, 1, s, hs, ?_⟩, Subtype.ext ?_⟩
  · rw [map_one, inv_mul_cancel₀ hs0]
  · exact mul_inv_cancel₀ hs0


end KerLE

theorem sub_C_eval_mem_span {R : Type*} [CommRing R] (v : Fin 2 → R) (p : MvPolynomial (Fin 2) R) :
    p - C (eval v p) ∈ Ideal.span {(X 0 - C (v 0) : MvPolynomial (Fin 2) R), X 1 - C (v 1)} := by
  induction p using MvPolynomial.induction_on with
  | C c => rw [eval_C, sub_self]; exact zero_mem _
  | add p r hp hr =>
    have : p + r - C (eval v (p + r)) = (p - C (eval v p)) + (r - C (eval v r)) := by rw [map_add, map_add]; ring
    rw [this]; exact add_mem hp hr
  | mul_X p i hp =>
    have : p * X i - C (eval v (p * X i)) = (p - C (eval v p)) * X i + C (eval v p) * (X i - C (v i)) := by
      rw [map_mul, eval_X, map_mul]; ring
    rw [this]
    refine add_mem (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ (Ideal.subset_span ?_))
    fin_cases i
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)

theorem ker_pointEval_eq_span (x y : A) (hx : red x = a) (hy : red y = b) (ϖ : A)
    (hϖ : ∀ c : A, red c = 0 ↔ ∃ d, c = ϖ * d) :
    RingHom.ker (pointEval A red a b) = Ideal.span {C ϖ, X 0 - C x, X 1 - C y} := by
  have hpe : ∀ p : MvPolynomial (Fin 2) A, pointEval A red a b p = red (eval ![x, y] p) := by
    intro p
    have hfun : (![a, b] : Fin 2 → k) = red ∘ ![x, y] := by
      funext i; fin_cases i <;> simp [hx, hy]
    rw [pointEval, coe_eval₂Hom, hfun, eval, coe_eval₂Hom, eval₂_comp_left, RingHom.comp_id]
  apply le_antisymm
  · intro p hp
    rw [RingHom.mem_ker, hpe] at hp
    obtain ⟨d, hd⟩ := (hϖ _).mp hp
    have : p = (p - C (eval ![x, y] p)) + C ϖ * C d := by rw [hd, map_mul]; ring
    rw [this]
    refine add_mem ?_ (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _)))
    exact Ideal.span_mono (Set.subset_insert _ _) (sub_C_eval_mem_span ![x, y] p)
  · rw [Ideal.span_le]
    rintro _ (rfl | rfl | rfl) <;> rw [SetLike.mem_coe, RingHom.mem_ker, hpe]
    · rw [eval_C]; exact (hϖ ϖ).mpr ⟨1, (mul_one _).symm⟩
    · simp
    · simp

end Presentation

end NodeLocalized
end ModularCurve

end
