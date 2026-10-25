/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.Comparison
import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
import Def.StatisticalMechanics.Code.FK.FiniteEnergy
open scoped BigOperators
open Module SimpleGraph


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem edgeRest_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (e : Sym2 V)
    (ω : ConfigSpace (Sym2 V)) : 0 < edgeRest G p e ω := by
  unfold edgeRest
  apply Finset.prod_pos
  intro e' _
  split
  · exact hp
  · linarith


theorem edgeProduct_setOpen (p : ℝ) {e : Sym2 V} (he : e ∈ G.edgeFinset)
    (ω : ConfigSpace (Sym2 V)) :
    edgeProduct G p (setOpen e ω) = edgeRest G p e ω * p := by
  unfold edgeProduct edgeRest
  rw [← Finset.prod_sdiff (Finset.singleton_subset_iff.mpr he)]
  have h1 : (∏ e' ∈ G.edgeFinset \ {e}, (if (setOpen e ω) e' then p else 1 - p))
      = ∏ e' ∈ G.edgeFinset \ {e}, (if ω e' then p else 1 - p) := by
    apply Finset.prod_congr rfl
    intro e' he'
    have : e' ≠ e := by
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at he'; exact he'.2
    rw [setOpen_of_ne this]
  rw [h1]
  simp [setOpen_self]


theorem edgeProduct_setClosed (p : ℝ) {e : Sym2 V} (he : e ∈ G.edgeFinset)
    (ω : ConfigSpace (Sym2 V)) :
    edgeProduct G p (setClosed e ω) = edgeRest G p e ω * (1 - p) := by
  unfold edgeProduct edgeRest
  rw [← Finset.prod_sdiff (Finset.singleton_subset_iff.mpr he)]
  have h1 : (∏ e' ∈ G.edgeFinset \ {e}, (if (setClosed e ω) e' then p else 1 - p))
      = ∏ e' ∈ G.edgeFinset \ {e}, (if ω e' then p else 1 - p) := by
    apply Finset.prod_congr rfl
    intro e' he'
    have : e' ≠ e := by
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at he'; exact he'.2
    rw [setClosed_of_ne this]
  rw [h1]
  simp [setClosed_self]


theorem fkWeight_lo {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {e : Sym2 V} (he : e ∈ G.edgeFinset) (ω : ConfigSpace (Sym2 V)) :
    (1 - p) * fkWeight G p q (setOpen e ω) ≤ p * fkWeight G p q (setClosed e ω) := by
  unfold fkWeight
  rw [edgeProduct_setOpen G p he, edgeProduct_setClosed G p he]
  set R := edgeRest G p e ω with hR
  set k1 := numClusters G (setOpen e ω)
  set k0 := numClusters G (setClosed e ω)
  have hRpos := edgeRest_pos G hp hp1 e ω
  have hpow : q ^ k1 ≤ q ^ k0 := pow_le_pow_right₀ hq (numClusters_setOpen_le G e ω)
  have hfac : (0 : ℝ) ≤ R * p * (1 - p) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hpow hfac]


theorem fkWeight_hi {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {e : Sym2 V} (he : e ∈ G.edgeFinset) (ω : ConfigSpace (Sym2 V)) :
    p * fkWeight G p q (setClosed e ω) ≤ q * (1 - p) * fkWeight G p q (setOpen e ω) := by
  unfold fkWeight
  rw [edgeProduct_setOpen G p he, edgeProduct_setClosed G p he]
  set R := edgeRest G p e ω with hR
  set k1 := numClusters G (setOpen e ω)
  set k0 := numClusters G (setClosed e ω)
  have hRpos := edgeRest_pos G hp hp1 e ω
  have hpow : q ^ k0 ≤ q ^ (k1 + 1) :=
    pow_le_pow_right₀ hq (numClusters_setClosed_le_setOpen_succ G e ω)
  rw [pow_succ] at hpow
  have hqp1 : (0 : ℝ) ≤ 1 - p := by linarith
  have hfac : (0 : ℝ) ≤ R * p * (1 - p) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hpow hfac]


end FK
end StatMech
