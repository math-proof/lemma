/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InhomogeneousFKG
import Theorem.StatisticalMechanics.Code.FK.RussoDerivativeBetaSum
import Theorem.StatisticalMechanics.Code.FK.FiniteEnergy.Part4
import Def.StatisticalMechanics.Code.FK.ActiveEdges.Part2
open scoped BigOperators
open Finset


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem activeWeight_pos {pf : Sym2 V → ℝ}
    (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 0 < q) (ω : ConfigSpace G.edgeSet) :
    0 < activeWeight G pf q ω :=
  fkWeightW_pos G hpf hpf1 hq (extendActive G ω)

theorem activeZ_pos {pf : Sym2 V → ℝ}
    (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 0 < q) : 0 < activeZ G pf q := by
  unfold activeZ
  exact Finset.sum_pos' (fun ω _ => (activeWeight_pos G hpf hpf1 hq ω).le)
    ⟨fun _ => false, Finset.mem_univ _, activeWeight_pos G hpf hpf1 hq _⟩

theorem activeProb_pos {pf : Sym2 V → ℝ}
    (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 0 < q) (ω : ConfigSpace G.edgeSet) :
    0 < activeProb G pf q ω := by
  exact div_pos (activeWeight_pos G hpf hpf1 hq ω) (activeZ_pos G hpf hpf1 hq)

theorem activeProb_sum_eq_one {pf : Sym2 V → ℝ}
    (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 0 < q) :
    ∑ ω, activeProb G pf q ω = 1 := by
  unfold activeProb activeZ
  rw [← Finset.sum_div]
  exact div_self (activeZ_pos G hpf hpf1 hq).ne'

theorem activeWeight_logSupermodular {pf : Sym2 V → ℝ}
    (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 1 ≤ q) (ω η : ConfigSpace G.edgeSet) :
    activeWeight G pf q ω * activeWeight G pf q η ≤
      activeWeight G pf q (ω ⊔ η) * activeWeight G pf q (ω ⊓ η) := by
  unfold activeWeight
  rw [extendActive_sup, extendActive_inf]
  exact fkWeightW_logSupermodular G hpf hpf1 hq _ _

theorem activeProb_FKGLatticeCondition {pf : Sym2 V → ℝ}
    (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 1 ≤ q) :
    FKGLatticeCondition (activeProb G pf q) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hZ : 0 < activeZ G pf q := activeZ_pos G hpf hpf1 hq0
  intro ω η
  unfold activeProb
  rw [div_mul_div_comm, div_mul_div_comm]
  exact (div_le_div_iff_of_pos_right (mul_pos hZ hZ)).mpr
    (activeWeight_logSupermodular G hpf hpf1 hq ω η)

lemma edgeProductW_setOpen (pf : Sym2 V → ℝ) (e : G.edgeSet)
    (ω : ConfigSpace (Sym2 V)) :
    edgeProductW G pf (setOpen e.1 ω) =
      (∏ a ∈ G.edgeFinset.erase e.1, (if ω a then pf a else 1 - pf a)) * pf e.1 := by
  unfold edgeProductW
  have he : e.1 ∈ G.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset]
    exact e.2
  rw [← Finset.prod_erase_mul _ _ he]
  congr 1
  · apply Finset.prod_congr rfl
    intro a ha
    rw [setOpen_of_ne]
    exact (Finset.mem_erase.mp ha).1
  · simp [setOpen_self]

lemma edgeProductW_setClosed (pf : Sym2 V → ℝ) (e : G.edgeSet)
    (ω : ConfigSpace (Sym2 V)) :
    edgeProductW G pf (setClosed e.1 ω) =
      (∏ a ∈ G.edgeFinset.erase e.1, (if ω a then pf a else 1 - pf a)) *
        (1 - pf e.1) := by
  unfold edgeProductW
  have he : e.1 ∈ G.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset]
    exact e.2
  rw [← Finset.prod_erase_mul _ _ he]
  congr 1
  · apply Finset.prod_congr rfl
    intro a ha
    rw [setClosed_of_ne]
    exact (Finset.mem_erase.mp ha).1
  · simp [setClosed_self]


theorem activeWeight_close_pair {pf : Sym2 V → ℝ}
    (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 1 ≤ q) (e : G.edgeSet) (ω : ConfigSpace G.edgeSet) :
    (1 - pf e.1) * activeWeight G pf q (setOpen e ω) ≤
      pf e.1 * activeWeight G pf q (setClosed e ω) := by
  unfold activeWeight fkWeightW
  rw [extendActive_setOpen, extendActive_setClosed,
    edgeProductW_setOpen, edgeProductW_setClosed]
  let R := ∏ a ∈ G.edgeFinset.erase e.1,
    (if extendActive G ω a then pf a else 1 - pf a)
  have hR : 0 ≤ R := by
    unfold R
    apply Finset.prod_nonneg
    intro a _
    split
    · exact (hpf a).le
    · linarith [hpf1 a]
  have hpow : q ^ numClusters G (setOpen e.1 (extendActive G ω)) ≤
      q ^ numClusters G (setClosed e.1 (extendActive G ω)) :=
    pow_le_pow_right₀ hq (numClusters_setOpen_le G e.1 (extendActive G ω))
  have hp : 0 ≤ pf e.1 * (1 - pf e.1) := mul_nonneg (hpf _).le (by linarith [hpf1 e.1])
  nlinarith [mul_le_mul_of_nonneg_left hpow (mul_nonneg hR hp)]

end FK
end StatMech
