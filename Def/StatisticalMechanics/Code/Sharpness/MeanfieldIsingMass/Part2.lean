/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingMass.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.DeltaBound.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.WeightedFieldGhost.Part2
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeDomain
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingMass
open Finset SimpleGraph
open scoped BigOperators symmDiff


namespace StatMech

namespace Sharpness

open FluxEdgeCopy

open FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def ghostFreeFinsetEquiv :
    Finset V ≃ {S : Finset (Option V) // none ∉ S} :=
  Equiv.ofBijective
    (fun T => (⟨T.map someEmb, by simp⟩ :
      {S : Finset (Option V) // none ∉ S}))
    ⟨by
      intro T U h
      apply Finset.map_injective someEmb
      exact Subtype.ext_iff.mp h,
    by
      intro S
      let T := S.1.preimage some (Set.injOn_of_injective someEmb.injective)
      refine ⟨T, Subtype.ext ?_⟩
      ext z
      cases z with
      | none => simp [S.2]
      | some z => simp [T]⟩


end Sharpness
end StatMech
