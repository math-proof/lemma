import Def.AlgebraicCurve_ChordalProximity
import Def.AlgebraicCurve_CycleChowForm

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve


theorem chowForm_zero {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) : chowForm s 0 = 1 :=
  Finsupp.prod_zero_index

theorem chowForm_single {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) (w : Place (AlgebraicClosure ℚ) F) (n : ℤ) :
    chowForm s (Finsupp.single w n)
      = (∑ i, MvPolynomial.C (evalVec s w i) * MvPolynomial.X i) ^ n.toNat :=
  Finsupp.prod_single_index (by simp)

theorem eval_chowForm {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) (Z : Divisor (AlgebraicClosure ℚ) F)
    (a : Fin r → AlgebraicClosure ℚ) :
    MvPolynomial.eval a (chowForm s Z) = Z.prod fun w n => (∑ i, evalVec s w i * a i) ^ n.toNat := by
  simp only [chowForm, map_finsuppProd, map_pow, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]

@[simp]
theorem secProd_zero {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) (k : ℕ) (u : F) : secProd s k u 0 = 1 :=
  Finsupp.prod_zero_index

theorem secProd_single {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) (k : ℕ) (u : F) (w : Place (AlgebraicClosure ℚ) F) (n : ℤ) :
    secProd s k u (Finsupp.single w n) = secVal s w k u ^ n.toNat :=
  Finsupp.prod_single_index (by simp)

theorem chowForm_isHomogeneous {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) (Z : Divisor (AlgebraicClosure ℚ) F) :
    (chowForm s Z).IsHomogeneous (Z.sum fun _ n => n.toNat) := by
  refine MvPolynomial.IsHomogeneous.prod Z.support _ (fun w => (Z w).toNat) fun w _ => ?_
  have h1 : (∑ i, MvPolynomial.C (evalVec s w i) * MvPolynomial.X i :
      MvPolynomial (Fin r) (AlgebraicClosure ℚ)).IsHomogeneous 1 :=
    MvPolynomial.IsHomogeneous.sum Finset.univ _ 1 fun i _ =>
      (MvPolynomial.isHomogeneous_X (AlgebraicClosure ℚ) i).C_mul (evalVec s w i)
  simpa only [one_mul] using h1.pow (Z w).toNat

theorem evalVec_pivotIndex {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) (w : Place (AlgebraicClosure ℚ) F) (hr : 0 < r)
    (h : s (pivotIndex s w hr) ≠ 0) : evalVec s w (pivotIndex s w hr) = 1 := by
  simp only [evalVec, dif_pos hr, mul_inv_cancel₀ h, Place.evalAt_one]

theorem linearForm_ne_zero {r : ℕ} {x : Fin r → AlgebraicClosure ℚ} {p : Fin r} (hp : x p = 1) :
    (∑ i, MvPolynomial.C (x i) * MvPolynomial.X i : MvPolynomial (Fin r) (AlgebraicClosure ℚ)) ≠ 0 := by
  intro h0
  have h1 := congrArg (MvPolynomial.eval (Pi.single p (1 : AlgebraicClosure ℚ))) h0
  simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, map_zero, Pi.single_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, hp] at h1
  exact one_ne_zero h1

theorem chowForm_ne_zero {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) (Z : Divisor (AlgebraicClosure ℚ) F)
    (h : ∀ w ∈ Z.support, ∃ p, evalVec s w p = 1) : chowForm s Z ≠ 0 := by
  rw [chowForm, Finsupp.prod, Finset.prod_ne_zero_iff]
  intro w hw
  obtain ⟨p, hp⟩ := h w hw
  exact pow_ne_zero _ (linearForm_ne_zero hp)

theorem totalDegree_chowForm {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) (Z : Divisor (AlgebraicClosure ℚ) F)
    (h : ∀ w ∈ Z.support, ∃ p, evalVec s w p = 1) :
    (chowForm s Z).totalDegree = Z.sum fun _ n => n.toNat :=
  (chowForm_isHomogeneous s Z).totalDegree (chowForm_ne_zero s Z h)

theorem norm_linearForm_apply_le {r : ℕ} (σ : AlgebraicClosure ℚ →+* ℂ)
    (x a : Fin r → AlgebraicClosure ℚ) :
    ‖σ (∑ i, x i * a i)‖ ≤ r * ((⨆ i, ‖σ (a i)‖) * ⨆ i, ‖σ (x i)‖) := by
  rw [map_sum]
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ i ∈ (Finset.univ : Finset (Fin r)),
      ‖σ (x i * a i)‖ ≤ (⨆ i, ‖σ (a i)‖) * ⨆ i, ‖σ (x i)‖ := fun i _ => by
    rw [map_mul, norm_mul, mul_comm]
    exact mul_le_mul (le_ciSup (f := fun i => ‖σ (a i)‖) (Finite.bddAbove_range _) i)
      (le_ciSup (f := fun i => ‖σ (x i)‖) (Finite.bddAbove_range _) i)
      (norm_nonneg _) (Real.iSup_nonneg fun _ => norm_nonneg _)
  refine (Finset.sum_le_card_nsmul _ _ _ h).trans ?_
  rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem norm_eval_chowForm_le {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → F) (Z : Divisor (AlgebraicClosure ℚ) F)
    (a : Fin r → AlgebraicClosure ℚ) :
    ‖σ (MvPolynomial.eval a (chowForm s Z))‖
      ≤ Z.prod fun w n => (r * ((⨆ i, ‖σ (a i)‖) * ⨆ i, ‖σ (evalVec s w i)‖)) ^ n.toNat := by
  rw [eval_chowForm, map_finsuppProd, Finsupp.prod, norm_prod, Finsupp.prod]
  refine Finset.prod_le_prod (fun w _ => norm_nonneg _) fun w _ => ?_
  rw [map_pow, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_linearForm_apply_le σ (evalVec s w) a) _

example {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] (s : Fin 0 → F)
    (E B : Divisor (AlgebraicClosure ℚ) F) (k : ℕ) (u : F) : ChowReciprocity s E k u B :=
  fun a _ _ _ _ _ ha => (ha (by simp [linSec])).elim

example {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ} (s : Fin r → F)
    (a : Fin r → AlgebraicClosure ℚ) : MvPolynomial.eval a (chowForm s 0) = 1 := by
  simp

end AlgebraicCurve

end
