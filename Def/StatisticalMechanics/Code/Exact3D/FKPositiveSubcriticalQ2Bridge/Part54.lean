/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part51
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

def finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupportEmbedding
    (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    (Sigma (fun m :
      {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ //
        m ∈ Ω} =>
      finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m.1 v)) ↪
      Sigma (fun m :
        ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
        finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v) where
  toFun a := ⟨a.1.1, a.2⟩
  inj' := by
    intro a b h
    cases a with
    | mk ma aa =>
      cases b with
      | mk mb bb =>
        rcases Sigma.mk.inj_iff.mp h with ⟨hmval, hbb⟩
        have hm : ma = mb := Subtype.ext hmval
        exact Sigma.ext hm hbb


noncomputable def finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport
    (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    Finset (Sigma (fun m :
      ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
      finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v)) :=
  (Ω.attach.sigma
      (fun m =>
        (Finset.univ :
          Finset
            (finiteBoundaryGhostDecrementedSourceWeightVertexFiber
              n m.1 v)))).map
    (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupportEmbedding
      n Ω v)


end Exact3D
end StatMech
