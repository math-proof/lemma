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
open Finset SimpleGraph
open scoped BigOperators symmDiff


namespace StatMech

namespace Sharpness

open FluxEdgeCopy

open FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def isingCutMass (beta : ℝ) (J : Sym2 V → ℝ)
    (g : V) (S : Finset V) : ℝ :=
  (currentSum G beta J ∅)⁻¹ ^ 2 *
    gatedSourcePairSum G beta J ∅ ∅
      (fun m => notConnComp G m g = S)


end Sharpness
end StatMech
