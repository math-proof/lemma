/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SignOrthantTiling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.BoxTiling.Part2
import Theorem.StatisticalMechanics.Code.FK.FKInterfaceSubadd.Part2
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Instance.StatisticalMechanics.Code.FK.SignOrthantTiling.Part3
open MeasureTheory Set Filter Topology Real
open scoped BigOperators
open SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxHeartbeats 1000000


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


theorem sot_orthantCrossSplit_satisfiable (t : ℝ) (j : ℕ) :
    sot_OrthantCrossSplit 0 t 0 j := by
  classical
  
  have hE0 : ∀ n, bxt_E 0 n = 0 := by
    intro n
    rw [bxt_E]
    have hc : (boxGraph 0 n).edgeFinset.card = 0 := by
      have hee : (boxGraph 0 n).edgeFinset = ∅ := by
        rw [SimpleGraph.edgeFinset_eq_empty, sot_boxGraph_zero_eq_bot]
      rw [hee, Finset.card_empty]
    rw [hc]; simp
  refine ⟨PEmpty, inferInstance, inferInstance, (⊥ : SimpleGraph PEmpty), inferInstance,
    (⊥ : SimpleGraph (boxVerts 0 (2 ^ j) ⊕ PEmpty)), inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · 
    refine ⟨?_, ?_, ?_⟩
    · intro x y hxy
      refine absurd hxy ?_
      match x, y with
      | Sum.inl a, Sum.inl b =>
        rw [SimpleGraph.sum_adj, sot_boxGraph_zero_eq_bot]; simp
      | Sum.inr c, Sum.inr d => rw [SimpleGraph.sum_adj]; simp
      | Sum.inl a, Sum.inr d => rw [SimpleGraph.sum_adj]; simp
      | Sum.inr c, Sum.inl b => rw [SimpleGraph.sum_adj]; simp
    · intro a b h; exact absurd h (by simp)
    · intro c d h; exact absurd h (by simp)
  · 
    refine ⟨?_⟩
    
    haveI : Unique (boxVerts 0 (2 ^ (j + 1))) :=
      uniqueOfSubsingleton (Classical.choice (sot_nonempty_boxVerts0 _))
    haveI : Nonempty (boxVerts 0 (2 ^ j) ⊕ PEmpty) :=
      ⟨Sum.inl (Classical.choice (sot_nonempty_boxVerts0 _))⟩
    haveI : Subsingleton (boxVerts 0 (2 ^ j) ⊕ PEmpty) := by
      constructor
      rintro (a | a) (b | b)
      · exact congrArg Sum.inl (Subsingleton.elim a b)
      · exact b.elim
      · exact a.elim
      · exact a.elim
    haveI : Unique (boxVerts 0 (2 ^ j) ⊕ PEmpty) :=
      uniqueOfSubsingleton (Classical.choice ‹Nonempty (boxVerts 0 (2 ^ j) ⊕ PEmpty)›)
    
    refine ⟨Equiv.ofUnique _ _, ?_⟩
    intro a b
    
    constructor
    · intro h
      
      exact absurd h (by simp)
    · intro h
      
      rw [sot_boxGraph_zero_eq_bot] at h
      exact absurd h (by simp)
  · 
    rw [show (2 : ℕ) ^ 0 - 1 = 0 by norm_num, pow_zero, sot_fkZ_bot_pempty]
  · 
    rw [zero_mul]
    have hle : (fis_interface (boxGraph 0 (2 ^ j)) (⊥ : SimpleGraph PEmpty)
        (⊥ : SimpleGraph (boxVerts 0 (2 ^ j) ⊕ PEmpty))) ⊆ ∅ := by
      rw [fis_interface]
      
      refine Finset.Subset.trans Finset.sdiff_subset ?_
      intro e he
      simp at he
    calc ((fis_interface (boxGraph 0 (2 ^ j)) (⊥ : SimpleGraph PEmpty)
            (⊥ : SimpleGraph (boxVerts 0 (2 ^ j) ⊕ PEmpty))).card : ℝ)
        ≤ ((∅ : Finset (Sym2 (boxVerts 0 (2 ^ j) ⊕ PEmpty))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hle
      _ = 0 := by simp
  · 
    rw [hE0, hE0]; simp


theorem sot_fk_uniqueness_of_orthantSplit (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (C : ℝ) (hC : 0 ≤ C)
    (hsplit : ∀ t, ∀ j, sot_OrthantCrossSplit d t C j)
    (hbdd : ∀ t, ∃ M : ℝ, ∀ j, |bxt_u d t (2 ^ j) / bxt_E d (2 ^ j)| ≤ M)
    (osc : ℝ → ℕ → ℝ) (hosc : ∀ t, Tendsto (osc t) atTop (𝓝 0))
    (hsand : ∀ t, ∀ n, 1 ≤ n → |ivp2_tiltFreeEnergy (boxGraph d n) 2 t
        - ivp2_tiltFreeEnergy (boxGraph d (2 ^ (Nat.log 2 n))) 2 t| ≤ osc t (Nat.log 2 n))
    (hfreeRot : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ocs_FreeRotationResidue (d := d) N e' t)
    (hwiredRot : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ocs_WiredRotationResidue (d := d) N e' t) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
  have hdoubling : ∀ t, bxt_NegLogDoublingBound d t := fun t =>
    sot_negLogDoublingBound_of_crossSplit d hd t C hC (hsplit t)
  exact bxt_fk_uniqueness_of_doubling hd N eb hEbox hdoubling hbdd osc hosc hsand hfreeRot hwiredRot


theorem sot_residue_remark : True := trivial

end FK
end StatMech
