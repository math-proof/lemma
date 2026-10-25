/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.LeeYangPolynomial
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangSingleEdge.Part3
import Theorem.StatisticalMechanics.Code.FrontierC.LeeYangSymmetry.Part2
import Def.StatisticalMechanics.Code.FrontierA.LeeYangAsano.Part14
open scoped ComplexConjugate


namespace StatMech.FrontierA

open scoped BigOperators

open StatMech.Ising StatMech.FrontierB StatMech.FrontierC

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
theorem leeYangChoiceWeight_eq_ofReal (beta : ℝ) (sigma : V → Bool) :
    leeYangChoiceWeight G beta (sigma, leeYangTauOf G sigma) =
      (leeYangRealChoiceWeight G beta sigma : ℂ) := by
  unfold leeYangChoiceWeight leeYangTauOf leeYangRealChoiceWeight
  push_cast
  apply Finset.prod_congr rfl
  intro e he
  by_cases h : sigma (leeYangEndpoint0 G e) = sigma (leeYangEndpoint1 G e)
  · simp [h]
  · simp [h, Complex.ofReal_exp]

omit [DecidableEq V] in
theorem leeYang_bond_endpoints (sigma : ConfigSpace V) (e : ↑G.edgeFinset) :
    bond sigma e.1 =
      if sigma (leeYangEndpoint0 G e) = sigma (leeYangEndpoint1 G e) then 1 else -1 := by
  rw [← leeYang_endpoints_mk G e, bond_mk]
  unfold spin
  cases h0 : sigma (leeYangEndpoint0 G e) <;>
      cases h1 : sigma (leeYangEndpoint1 G e) <;> simp

omit [DecidableEq V] in
theorem exp_card_mul_leeYangRealChoiceWeight (beta : ℝ) (sigma : ConfigSpace V) :
    Real.exp (beta * G.edgeFinset.card) * leeYangRealChoiceWeight G beta sigma =
      zeroFieldInteractionWeight G beta sigma := by
  have hattach : G.edgeFinset.attach =
      (Finset.univ : Finset (↑G.edgeFinset)) := by
    ext e
    simp
  have hsum : (∑ e ∈ G.edgeFinset, bond sigma e) =
      ∑ e : ↑G.edgeFinset, bond sigma e.1 := by
    rw [← Finset.sum_attach]
    rw [hattach]
  have hexpcard : Real.exp (beta * G.edgeFinset.card) =
      ∏ _e : ↑G.edgeFinset, Real.exp beta := by
    change Real.exp (beta * G.edgeFinset.card) =
      ∏ e ∈ (Finset.univ : Finset (↑G.edgeFinset)), Real.exp beta
    rw [Finset.prod_const, ← Real.exp_nat_mul]
    congr 1
    rw [Finset.card_univ, Fintype.card_coe]
    ring
  unfold zeroFieldInteractionWeight leeYangRealChoiceWeight
  rw [hsum, Finset.mul_sum, Real.exp_sum, hexpcard]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e he
  rw [leeYang_bond_endpoints]
  by_cases h : sigma (leeYangEndpoint0 G e) = sigma (leeYangEndpoint1 G e)
  · simp [h]
  · rw [if_neg h, if_neg h, ← Real.exp_add]
    congr 1
    ring

theorem eval_leeYangComplexPolynomial (beta : ℝ) (q : ℂ) :
    (leeYangComplexPolynomial G beta).eval q =
      ∑ s : ConfigSpace V,
        (zeroFieldInteractionWeight G beta s : ℂ) * q ^ minusSpinCount s := by
  simp [leeYangComplexPolynomial, leeYangPolynomial]

theorem leeYangContractedProduct_diagonal (beta : ℝ) (q : ℂ) :
    (Real.exp (beta * G.edgeFinset.card) : ℂ) *
        leeYangContractedProduct G beta (leeYangDiagonal G q) =
      (leeYangComplexPolynomial G beta).eval q := by
  rw [leeYangContractedProduct_eq_sum_sigma, Finset.mul_sum,
    eval_leeYangComplexPolynomial]
  let F : ConfigSpace V → ℂ := fun sigma ↦
    (Real.exp (beta * G.edgeFinset.card) : ℂ) *
      (leeYangChoiceWeight G beta (sigma, leeYangTauOf G sigma) *
        leeYangMonomial (leeYangAnchorSupport G sigma) (leeYangDiagonal G q))
  change (∑ sigma : ConfigSpace V, F sigma) = _
  rw [show (∑ sigma : ConfigSpace V, F sigma) =
      ∑ s : ConfigSpace V, F (leeYangFlipEquiv s) by
        simpa using (Equiv.sum_comp leeYangFlipEquiv F).symm]
  apply Finset.sum_congr rfl
  intro s hs
  have hcount :
      (Finset.univ.filter fun v ↦ leeYangFlip s v = true).card =
        minusSpinCount s := by
    unfold minusSpinCount leeYangFlip
    congr 1
    ext v
    cases h : s v <;> simp [h]
  have hweight :
      (Real.exp (beta * G.edgeFinset.card) : ℂ) *
          leeYangChoiceWeight G beta
            (leeYangFlip s, leeYangTauOf G (leeYangFlip s)) =
        (zeroFieldInteractionWeight G beta s : ℂ) := by
    rw [leeYangChoiceWeight_eq_ofReal]
    rw [← Complex.ofReal_mul]
    rw [exp_card_mul_leeYangRealChoiceWeight]
    rw [zeroFieldInteractionWeight_flip]
  simp only [F, leeYangFlipEquiv_apply]
  rw [← mul_assoc, hweight, leeYangMonomial_anchorSupport_diagonal, hcount]

theorem leeYangComplexPolynomial_ne_zero_in_openUnitDisk
    {beta : ℝ} (hbeta : 0 ≤ beta) {q : ℂ} (hq : ‖q‖ < 1) :
    (leeYangComplexPolynomial G beta).eval q ≠ 0 := by
  have hcontracted :
      leeYangContractedProduct G beta (leeYangDiagonal G q) ≠ 0 := by
    apply leeYangContractedProduct_stable G hbeta
    intro k
    rcases k with v | ⟨v, e⟩
    · exact hq
    · simp [leeYangDiagonal]
  intro heval
  have hprod :
      (Real.exp (beta * G.edgeFinset.card) : ℂ) *
          leeYangContractedProduct G beta (leeYangDiagonal G q) = 0 := by
    rw [leeYangContractedProduct_diagonal, heval]
  exact hcontracted ((mul_eq_zero.mp hprod).resolve_left (by
    exact_mod_cast Real.exp_ne_zero (beta * G.edgeFinset.card)))


theorem finiteGraph_hasLeeYangCircle {beta : ℝ} (hbeta : 0 ≤ beta) :
    HasLeeYangCircle G beta := by
  intro z hz
  have hge : 1 ≤ ‖z‖ := by
    exact not_lt.mp (fun hlt ↦
      leeYangComplexPolynomial_ne_zero_in_openUnitDisk G hbeta hlt hz)
  have hle : ‖z‖ ≤ 1 := by
    by_contra h
    have hgt : 1 < ‖z‖ := lt_of_not_ge h
    have hinvnorm : ‖z⁻¹‖ < 1 := by
      rw [norm_inv]
      exact inv_lt_one_of_one_lt₀ hgt
    have hinvroot : (leeYangComplexPolynomial G beta).eval z⁻¹ = 0 :=
      (leeYangComplexPolynomial_eval_inv_eq_zero_iff' G beta z).2 hz
    exact leeYangComplexPolynomial_ne_zero_in_openUnitDisk G hbeta hinvnorm hinvroot
  exact le_antisymm hle hge

end StatMech.FrontierA
