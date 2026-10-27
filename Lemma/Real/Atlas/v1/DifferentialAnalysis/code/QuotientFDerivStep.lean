import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.DifferentialAnalysis.code.QuotientFDerivStep
open MvPolynomial Complex DifferentialOperators


namespace DifferentialOperators

/--
[coordCLM_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/QuotientFDerivStep.lean)
-/
@[path]
lemma coordCLM_apply
  {n : ℕ}
  {i : Fin n}
  {ξ : EuclideanSpace ℝ (Fin n)} :
-- imply
  coordCLM i ξ = (ξ i : ℂ) := by
-- proof
simp [coordCLM, PiLp.proj]

end DifferentialOperators

namespace DifferentialOperators

/--
[evalAtReal_differentiable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/QuotientFDerivStep.lean)
-/
@[path]
lemma evalAtReal_differentiable
  {n : ℕ}
  {Q : MvPolynomial (Fin n) ℂ} :
-- imply
  Differentiable ℝ (evalAtReal Q) := by
-- proof
  unfold evalAtReal
  induction Q using MvPolynomial.induction_on with
  | C c => simp only [eval_C]; exact differentiable_const c
  | add p q hp hq =>
    have h : (fun ξ : EuclideanSpace ℝ (Fin n) => (p + q).eval (fun i => (ξ i : ℂ))) =
      (fun ξ => p.eval (fun i => (ξ i : ℂ)) + q.eval (fun i => (ξ i : ℂ))) := by
      ext ξ; simp [map_add]
    rw [h]; exact hp.add hq
  | mul_X p i hp =>
    have h : (fun ξ : EuclideanSpace ℝ (Fin n) => (p * X i).eval (fun i => (ξ i : ℂ))) =
      (fun ξ => p.eval (fun i => (ξ i : ℂ)) * (ξ i : ℂ)) := by
      ext ξ; simp [eval_mul, eval_X]
    rw [h]; exact hp.mul (ofRealCLM.differentiable.comp (by fun_prop))

end DifferentialOperators

namespace DifferentialOperators

/--
[fderiv_evalAtReal_single](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/QuotientFDerivStep.lean)
-/
@[path]
lemma fderiv_evalAtReal_single
  {n : ℕ}
  {Q : MvPolynomial (Fin n) ℂ}
  {j : Fin n}
  {ξ : EuclideanSpace ℝ (Fin n)} :
-- imply
  fderiv ℝ (evalAtReal Q) ξ (EuclideanSpace.single j 1) = evalAtReal (pderiv j Q) ξ := by
-- proof
  unfold evalAtReal
  induction Q using MvPolynomial.induction_on with
  | C c =>
    have : (fun ξ' : EuclideanSpace ℝ (Fin n) => eval (fun i => (ξ' i : ℂ)) (C c)) =
      fun _ => c := by ext; simp [eval_C]
    rw [this]; simp
  | add p q hp hq =>
    have hfun : (fun ξ' : EuclideanSpace ℝ (Fin n) => eval (fun i => (ξ' i : ℂ)) (p + q)) =
      (fun ξ' => eval (fun i => (ξ' i : ℂ)) p + eval (fun i => (ξ' i : ℂ)) q) := by
      ext; simp [map_add]
    rw [hfun]
    have hdp := (evalAtReal_differentiable (n := n) p).differentiableAt (x := ξ)
    have hdq := (evalAtReal_differentiable (n := n) q).differentiableAt (x := ξ)
    have key : fderiv ℝ (fun ξ' : EuclideanSpace ℝ (Fin n) =>
      eval (fun i => (ξ' i : ℂ)) p + eval (fun i => (ξ' i : ℂ)) q) ξ =
      fderiv ℝ (fun ξ' => eval (fun i => (ξ' i : ℂ)) p) ξ +
      fderiv ℝ (fun ξ' => eval (fun i => (ξ' i : ℂ)) q) ξ :=
      (hdp.hasFDerivAt.add hdq.hasFDerivAt).fderiv
    rw [key, ContinuousLinearMap.add_apply, hp, hq, map_add, eval_add]
  | mul_X p i hp =>
    have hfun : (fun ξ' : EuclideanSpace ℝ (Fin n) => eval (fun i => (ξ' i : ℂ)) (p * X i)) =
      (fun ξ' => eval (fun i => (ξ' i : ℂ)) p * (ξ' i : ℂ)) := by
      ext; simp [eval_mul, eval_X]
    rw [hfun]
    have hdp := (evalAtReal_differentiable (n := n) p).differentiableAt (x := ξ)
    have hdc : HasFDerivAt (fun ξ' : EuclideanSpace ℝ (Fin n) => (ξ' i : ℂ))
      (coordCLM i) ξ := by
      have : (fun ξ' : EuclideanSpace ℝ (Fin n) => (ξ' i : ℂ)) = coordCLM i := by
        ext v; simp
      rw [this]; exact (coordCLM i).hasFDerivAt
    have key : fderiv ℝ (fun ξ' : EuclideanSpace ℝ (Fin n) =>
      eval (fun k => (ξ' k : ℂ)) p * (ξ' i : ℂ)) ξ =
      eval (fun k => (ξ k : ℂ)) p • coordCLM i +
      (ξ i : ℂ) • fderiv ℝ (fun ξ' => eval (fun k => (ξ' k : ℂ)) p) ξ :=
      (hdp.hasFDerivAt.mul hdc).fderiv
    rw [key, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply, hp, coordCLM_apply,
      pderiv_mul, eval_add, eval_mul, eval_mul, eval_X, pderiv_X]
    simp only [Pi.single_apply, smul_eq_mul]
    simp only [EuclideanSpace.single, PiLp.single, Pi.single_apply]
    split_ifs with h
    · subst h; simp only [map_one]; push_cast; ring
    · simp only [map_zero]; push_cast; ring

end DifferentialOperators

namespace DifferentialOperators

/--
[hasDerivAt_curve](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/QuotientFDerivStep.lean)
-/
@[path]
lemma hasDerivAt_curve
  {n : ℕ}
  {ξ : EuclideanSpace ℝ (Fin n)}
  {j : Fin n} :
-- imply
  HasDerivAt (fun t : ℝ => ξ + t • EuclideanSpace.single j (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) 0 := by
-- proof
  have h : HasDerivAt (fun t : ℝ => t • EuclideanSpace.single j (1 : ℝ))
    ((1 : ℝ) • EuclideanSpace.single j (1 : ℝ)) 0 :=
    (hasDerivAt_id (0 : ℝ)).smul_const _
  simp only [one_smul] at h
  have := (hasDerivAt_const 0 ξ).add h
  simp only [zero_add] at this
  exact this

end DifferentialOperators

namespace DifferentialOperators

/--
[quotient_fderiv_step](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/QuotientFDerivStep.lean)
-/
@[path]
lemma quotient_fderiv_step
  {n : ℕ}
  {P Q : MvPolynomial (Fin n) ℂ}
  {k : ℕ}
  {j : Fin n}
  {ξ : EuclideanSpace ℝ (Fin n)}
-- given
  (hP : evalAtReal P ξ ≠ 0) :
-- imply
  fderiv ℝ (fun ξ' => evalAtReal Q ξ' / (evalAtReal P ξ') ^ k) ξ (EuclideanSpace.single j 1) = evalAtReal (P * pderiv j Q - (k : ℕ) • (Q * pderiv j P)) ξ / (evalAtReal P ξ) ^ (k + 1) := by
-- proof
  set eⱼ := EuclideanSpace.single j (1 : ℝ)
  set γ := fun t : ℝ => ξ + t • eⱼ
  have hγ : HasDerivAt γ eⱼ 0 := hasDerivAt_curve ξ j
  have hγ0 : γ 0 = ξ := by simp [γ]
  set Qγ := fun t : ℝ => evalAtReal Q (γ t)
  set Pγ := fun t : ℝ => evalAtReal P (γ t)
  have hQ_da := (evalAtReal_differentiable Q).differentiableAt (x := ξ)
  have hP_da := (evalAtReal_differentiable P).differentiableAt (x := ξ)
  have hPk_ne : (evalAtReal P ξ) ^ k ≠ 0 := pow_ne_zero k hP
  have hQγ : HasDerivAt Qγ (evalAtReal (pderiv j Q) ξ) 0 := by
    show HasDerivAt (evalAtReal Q ∘ γ) _ 0
    have := (hγ0 ▸ hQ_da.hasFDerivAt).comp_hasDerivAt 0 hγ
    rwa [hγ0, fderiv_evalAtReal_single] at this
  have hPγ : HasDerivAt Pγ (evalAtReal (pderiv j P) ξ) 0 := by
    show HasDerivAt (evalAtReal P ∘ γ) _ 0
    have := (hγ0 ▸ hP_da.hasFDerivAt).comp_hasDerivAt 0 hγ
    rwa [hγ0, fderiv_evalAtReal_single] at this
  have hPkγ : HasDerivAt (fun t => Pγ t ^ k)
    ((k : ℂ) * Pγ 0 ^ (k - 1) * evalAtReal (pderiv j P) ξ) 0 :=
    hPγ.pow k
  have hPγ0 : Pγ 0 = evalAtReal P ξ := by simp [Pγ, hγ0]
  have hPk0 : Pγ 0 ^ k ≠ 0 := hPγ0 ▸ hPk_ne
  have hdiv : HasDerivAt (fun t => Qγ t / Pγ t ^ k)
    ((evalAtReal (pderiv j Q) ξ * Pγ 0 ^ k -
      Qγ 0 * ((k : ℂ) * Pγ 0 ^ (k - 1) * evalAtReal (pderiv j P) ξ)) /
      (Pγ 0 ^ k) ^ 2) 0 :=
    hQγ.div hPkγ hPk0
  have hfγ : HasDerivAt (fun t => evalAtReal Q (γ t) / (evalAtReal P (γ t)) ^ k)
    (fderiv ℝ (fun ξ' => evalAtReal Q ξ' / (evalAtReal P ξ') ^ k) ξ eⱼ) 0 := by
    have hf_da : DifferentiableAt ℝ (fun ξ' => evalAtReal Q ξ' / (evalAtReal P ξ') ^ k) ξ :=
      hQ_da.mul ((hP_da.pow k).inv hPk_ne)
    have := (hγ0 ▸ hf_da.hasFDerivAt).comp_hasDerivAt 0 hγ
    rwa [hγ0] at this
  have huniq := hfγ.unique hdiv
  rw [huniq]
  simp only [hγ0, Qγ, Pγ]
  simp only [evalAtReal, map_sub, map_mul, map_nsmul]
  have hPne : evalAtReal P ξ ≠ 0 := hP
  simp only [evalAtReal] at hPne
  set p := (eval fun i => (ξ i : ℂ)) P
  set q := (eval fun i => (ξ i : ℂ)) Q
  set dq := (eval fun i => (ξ i : ℂ)) (pderiv j Q)
  set dp := (eval fun i => (ξ i : ℂ)) (pderiv j P)
  have hp_ne : p ≠ 0 := hPne
  have hpk_ne : p ^ k ≠ 0 := pow_ne_zero k hp_ne
  rw [nsmul_eq_mul, Nat.cast_comm]
  field_simp [hp_ne, hpk_ne]
  obtain _ | k := k
  · simp
  · simp only [Nat.succ_sub_one, pow_succ]
    ring
end DifferentialOperators



-- created on 2026-10-23
