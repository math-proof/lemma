/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonLieb.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsingFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.IsingSharpnessFull.Part2
import Def.StatisticalMechanics.Code.Sharpness.SimonLieb
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

section SimonWeight

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem tanh_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Real.tanh t := by
  rw [Real.tanh_eq_sinh_div_cosh]
  refine div_nonneg ?_ (Real.cosh_pos t).le
  rw [show (0 : ℝ) = Real.sinh 0 from by simp]
  exact Real.sinh_le_sinh.mpr ht


theorem simonWeight_nonneg (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (o : V) (hβ : 0 ≤ β)
    (hJ : ∀ e, 0 ≤ J e)
    (hcorr : ∀ x, 0 ≤ expectationJ G β (couplingIn J S) {o, x}) :
    ∀ x y, 0 ≤ simonWeight G β J S o x y := by
  intro x y
  unfold simonWeight
  exact mul_nonneg (tanh_nonneg (mul_nonneg hβ (hJ _))) (hcorr x)


theorem localized_correlation_of_claim2 (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (g : V)
    (hg : g ∉ S) (o x : V) (h0 : o ∈ S) (hx : x ∈ S)
    (hZ : currentSum G β (couplingIn J S) ∅ ≠ 0)
    (hden : (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
          (if sources G (ofEdgeFun G pq.1) = ∅ then weight G β J (ofEdgeFun G pq.1) else 0)
            * (if sources G (ofEdgeFun G pq.2) = ∅ then weight G β J (ofEdgeFun G pq.2) else 0)
            * (if notConnComp G (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) g = S
                then 1 else 0)) ≠ 0) :
    expectationJ G β (couplingIn J S) {o, x}
      = (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
          (if sources G (ofEdgeFun G pq.1) = {o, x} then weight G β J (ofEdgeFun G pq.1) else 0)
            * (if sources G (ofEdgeFun G pq.2) = ∅ then weight G β J (ofEdgeFun G pq.2) else 0)
            * (if notConnComp G (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) g = S
                then 1 else 0))
        / (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
          (if sources G (ofEdgeFun G pq.1) = ∅ then weight G β J (ofEdgeFun G pq.1) else 0)
            * (if sources G (ofEdgeFun G pq.2) = ∅ then weight G β J (ofEdgeFun G pq.2) else 0)
            * (if notConnComp G (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) g = S
                then 1 else 0)) :=
  localized_two_point_of_claim2 G β J S g hg o x h0 hx hZ hden

end SimonWeight


section Reduction

variable {V : Type*}


theorem simonLieb_of_firstExit (τ : V → V → ℝ) (o : V) (S : Finset V)
    (simWeight : V → V → ℝ) (boundaryTargets : Finset V)
    (hτ : ∀ a b, 0 ≤ τ a b) (hw : ∀ x y, 0 ≤ simWeight x y)
    (hbound : ∀ z, z ∉ S →
      τ o z ≤ ∑ x ∈ S, ∑ y ∈ boundaryTargets, simWeight x y * τ y z) :
    SimonLieb τ o S simWeight boundaryTargets where
  τ_nonneg := hτ
  weight_nonneg := hw
  simon := hbound


theorem simonLieb_simonWeight [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (o : V) (boundaryTargets : Finset V)
    (τ : V → V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (hcorr : ∀ x, 0 ≤ expectationJ G β (couplingIn J S) {o, x})
    (hτ : ∀ a b, 0 ≤ τ a b)
    (hbound : ∀ z, z ∉ S →
      τ o z ≤ ∑ x ∈ S, ∑ y ∈ boundaryTargets,
        simonWeight G β J S o x y * τ y z) :
    SimonLieb τ o S (simonWeight G β J S o) boundaryTargets :=
  simonLieb_of_firstExit τ o S (simonWeight G β J S o) boundaryTargets hτ
    (simonWeight_nonneg G β J S o hβ hJ hcorr) hbound


theorem simonConst_simonWeight_nonneg [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (o : V)
    (boundaryTargets : Finset V) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (hcorr : ∀ x, 0 ≤ expectationJ G β (couplingIn J S) {o, x}) :
    0 ≤ simonConst S (simonWeight G β J S o) boundaryTargets :=
  simonConst_nonneg S (simonWeight G β J S o) boundaryTargets
    (simonWeight_nonneg G β J S o hβ hJ hcorr)

end Reduction
end Sharpness
end StatMech
