/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierGeneral.Part5
import Def.StatisticalMechanics.Code.Ising.KramersWannierEvenToCut.Part6
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section Reduction

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Gp Gd : SimpleGraph V} [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]


section SingleCycle

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Gp Gd : SimpleGraph V} [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]


omit [Fintype V] in


theorem cycleParityCompatible_of_decomposition (ψ : Sym2 V ≃ Sym2 V)
    {cycleSets : Finset (Sym2 V) → Prop} (hsingle : SingleDualCycleParity Gp ψ cycleSets)
    {F : Finset (Sym2 V)} {ι : Type*} (s : Finset ι)
    (pieces : ι → Finset (Sym2 V))
    (hcov : F = s.biUnion pieces)
    (hdisj : (s : Set ι).PairwiseDisjoint pieces)
    (hcyc : ∀ i ∈ s, cycleSets (pieces i)) :
    CycleParityCompatible Gp ψ F := by
  classical
  change EvenOnCycles Gp (F.image ψ.symm)
  rw [hcov]
  
  have himg : (s.biUnion pieces).image ψ.symm
      = s.biUnion (fun i => (pieces i).image ψ.symm) := Finset.biUnion_image
  rw [himg]
  refine evenOnCycles_biUnion s (fun i => (pieces i).image ψ.symm) ?_ ?_
  · 
    intro i hi j hj hij
    have hd := hdisj hi hj hij
    
    apply Finset.disjoint_left.mpr
    intro e hei hej
    rw [Finset.mem_image] at hei hej
    obtain ⟨a, ha, rfl⟩ := hei
    obtain ⟨b, hb, hba⟩ := hej
    have hab : a = b := ψ.symm.injective hba.symm
    subst hab
    exact (Finset.disjoint_left.mp hd ha) hb
  · intro i hi
    exact hsingle (pieces i) (hcyc i hi)

end SingleCycle
end Reduction
end Ising
end StatMech
