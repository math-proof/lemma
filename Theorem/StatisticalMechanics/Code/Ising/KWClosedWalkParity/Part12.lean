/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierEvenToCut.Part8
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
import Def.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part9
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section RegionSide

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Gp Gd : SimpleGraph V} [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]


omit [Fintype V] [DecidableRel Gd.Adj] in


theorem dualWalkBoundsRegion_of_edgeless (ψ : Sym2 V ≃ Sym2 V) (hGd : Gd.edgeSet = ∅) :
    DualWalkBoundsRegion Gp Gd ψ := by
  intro w W
  refine ⟨fun _ => false, ?_⟩
  intro u v _
  have hnil : W.edges = [] := edges_eq_nil_of_isEmpty_edgeSet hGd W
  have hempty : (W.edges.toFinset).image ψ.symm = (∅ : Finset (Sym2 V)) := by
    rw [hnil]; simp
  rw [hempty]
  simp

end RegionSide
end Ising
end StatMech
