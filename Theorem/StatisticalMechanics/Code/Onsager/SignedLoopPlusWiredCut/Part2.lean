/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusWiredCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopAnchoredCut
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempPlus.Part3
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Def.StatisticalMechanics.Code.Onsager.SignedLoopPlusWiredCut.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA

noncomputable section

theorem ons_plusWiredCutLattice_eq_fvCutEdges
    (d n : Nat) (tau : {x // x ∈ box d n} → Bool) :
    ons_plusWiredCutLattice d n tau =
      ons_fvCutEdges (bondFinsetTouch d n) (glue (plusField d) tau) := by
  ext edge
  constructor
  · intro hedge
    rw [ons_plusWiredCutLattice, Finset.mem_map] at hedge
    obtain ⟨typed, htyped, rfl⟩ := hedge
    exact (mem_plusWiredCut_iff d n tau typed).mp htyped
  · intro hedge
    have hedgeB : edge ∈ bondFinsetTouch d n := by
      exact (Finset.mem_filter.mp hedge).1
    let typed : ons_PlusWiredBond d n := ⟨edge, hedgeB⟩
    rw [ons_plusWiredCutLattice, Finset.mem_map]
    exact ⟨typed, (mem_plusWiredCut_iff d n tau typed).mpr hedge, rfl⟩


theorem card_plusWiredCut_eq_fvCutEdges
    (d n : Nat) (tau : {x // x ∈ box d n} → Bool) :
    (multibondCut (ons_plusWiredBondEnds d n)
        (ons_optionAnchoredEquiv tau).1).card =
      (ons_fvCutEdges (bondFinsetTouch d n)
        (glue (plusField d) tau)).card := by
  rw [← ons_plusWiredCutLattice_eq_fvCutEdges d n tau,
    ons_plusWiredCutLattice, Finset.card_map]


end
end StatMech.Onsager
