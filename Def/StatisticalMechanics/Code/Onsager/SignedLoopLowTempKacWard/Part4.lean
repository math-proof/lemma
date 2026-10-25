/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempDual.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardArbitraryValenceClosure
import Instance.StatisticalMechanics.Code.Onsager.SignedLoopLowTempKacWard.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice

open StatMech.FrontierA

noncomputable section

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E]

noncomputable def kwg_subdivEvenEquiv (ends : E -> Sym2 V) :
    KWGIndexedEvenSet ends ≃ KWActualEvenSubgraph (kwg_subdivGraph ends) where
  toFun F := ⟨kwg_subdivLift ends F.1,
    (kwg_subdivLift_mem_evenSubgraphs_iff ends F.1).mpr F.2⟩
  invFun H := ⟨kwg_subdivExtract H.1, by
    have hH := H.2
    rw [← kwg_subdivLift_extract_of_even ends H.1 H.2] at hH
    exact (kwg_subdivLift_mem_evenSubgraphs_iff ends _).mp hH⟩
  left_inv F := by
    apply Subtype.ext
    exact kwg_subdivExtract_lift ends F.1
  right_inv H := by
    apply Subtype.ext
    exact kwg_subdivLift_extract_of_even ends H.1 H.2

end
end StatMech.Onsager
