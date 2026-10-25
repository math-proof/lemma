/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDenseIncidencePrimitiveBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPrimitiveValueBridge
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialMultiCellRegularity.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge
open Filter Set Topology


namespace StatMech.Universality

noncomputable section

namespace FKIsingDenseIncidenceFamily

variable {N : Nat -> Nat} {hN : forall k, 0 < N k}

variable {mesh : Nat -> Real}


theorem discreteVertexPrimitive_tendsto
    {Phi : Complex -> Complex} {bulkRate layerRate : Nat -> Real}
    (D : FKIsingDenseIncidenceFamily N hN mesh)
    (H : FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalSplitRobinConsistencyInputs
      N hN Phi mesh bulkRate layerRate)
    (lipschitzConstant : NNReal)
    (hPhi : LipschitzWith lipschitzConstant (fun z => (Phi z).im))
    (j : Nat) :
    Tendsto (fun k => D.discreteVertexPrimitive j k)
      atTop (nhds (Phi (D.point j)).im) := by
  exact
    (H.primitive_tendsto_at_of_incidenceEmbedding lipschitzConstant hPhi
      (D.incidence j) (D.point j) (D.embedding_tendsto j)).1

end FKIsingDenseIncidenceFamily
end
end StatMech.Universality
