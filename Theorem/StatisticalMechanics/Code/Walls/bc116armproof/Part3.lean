/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc116armproof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc114haschild.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc101mengergap
import Def.StatisticalMechanics.Code.Walls.bc116armproof.Part2
open Set SimpleGraph Finset

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}


theorem bc116_armCovered_concrete_of_membership (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d)
    {B H : Site d → Prop} (hmem : bc116_ArmPathMembership ω L y B H) :
    bc114_ArmCovered (bc67_contractedLattice ω L y) B H :=
  bc116_armCovered_of_throughPathCovered (bc67_contractedLattice ω L y) hmem


theorem bc116_status :
    
    (∀ (F : SimpleGraph V) (B H : V → Prop),
      bc116_ThroughPathCovered F B H → bc114_ArmCovered F B H) ∧
    
    (∀ (F : SimpleGraph V) (v : V), bc114_IsInternal F v →
      ∃ (s t : V) (p : F.Walk s t), p.IsPath ∧ v ∈ p.support ∧ v ≠ s ∧ v ≠ t) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 1 ≤ R → ∀ (y a : Site d), a ∈ box d R →
      (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite →
      ∃ z ∈ vertexBoundary d R, ∃ _p : (bc67_contractedLattice ω L y).Walk a z, True) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) (B H : Site d → Prop),
      bc116_ArmPathMembership ω L y B H →
      bc114_ArmCovered (bc67_contractedLattice ω L y) B H) ∧
    
    (∀ (F : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel F.Adj] (v : V),
      F.degree v = 1 → ¬ bc114_IsInternal F v) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro F B H hcov; exact bc116_armCovered_of_throughPathCovered F hcov
  · intro F v hv
    obtain ⟨s, t, p, i, hp, hi0, hilt, hveq⟩ := hv
    subst hveq
    refine ⟨s, t, p, hp, p.getVert_mem_support i, ?_, ?_⟩
    · intro h
      have h0 : p.getVert i = p.getVert 0 := by rw [p.getVert_zero]; exact h
      exact absurd (hp.getVert_injOn (by simp; omega) (by simp) h0) (by omega)
    · intro h
      have hL : p.getVert i = p.getVert p.length := by rw [p.getVert_length]; exact h
      exact absurd (hp.getVert_injOn (by simp; omega) (by simp) hL) (by omega)
  · intro ω L R hR y a habox hinf
    exact bc116_arm_boundary_path_concrete ω L R hR y a habox hinf
  · intro ω L y B H hmem
    exact bc116_armCovered_concrete_of_membership ω L y hmem
  · intro F _ _ _ v hdeg
    exact bc116_pendant_not_covered F hdeg

end StatMech.Walls
