/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteActiveDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights.Part4
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Def.StatisticalMechanics.Code.FK.FiniteActiveDuality
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.FK

open Lattice

noncomputable section

variable {V W : Type*} [Fintype V] [Fintype W]
  [DecidableEq V] [DecidableEq W]
  (G : SimpleGraph V) (H : SimpleGraph W)
  [DecidableRel G.Adj] [DecidableRel H.Adj]


@[simp] theorem activeDualConfig_apply
    (edgeDual : G.edgeSet ≃ H.edgeSet)
    (omega : ConfigSpace G.edgeSet) (e : H.edgeSet) :
    activeDualConfig G H edgeDual omega e =
      !(omega (edgeDual.symm e)) := rfl

@[simp] theorem activeDualConfig_symm_apply
    (edgeDual : G.edgeSet ≃ H.edgeSet)
    (eta : ConfigSpace H.edgeSet) (e : G.edgeSet) :
    (activeDualConfig G H edgeDual).symm eta e =
      !(eta (edgeDual e)) := rfl


end
end StatMech.FK
