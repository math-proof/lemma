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
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part17
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

noncomputable def edgeCopySourcePairSum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V) : ℝ :=
  ∑' m : ↥G.edgeFinset → ℕ,
    (∑ S : Finset (Sharpness.FluxEdgeCopy.Copy G m),
      (if Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m) S = A then
        (1 : ℝ)
      else
        0) *
        (if Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM G m) (Finset.univ \ S) = B then
          1
        else
          0)) *
      Sharpness.weight G β J (Sharpness.ofEdgeFun G m)


noncomputable def edgeCopySourcePairEmptyCollapsedSum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) : ℝ :=
  ∑' m : ↥G.edgeFinset → ℕ,
    ((if Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) = A then
        (1 : ℝ)
      else
        0) *
      (((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)).powerset.filter
        (fun K =>
          Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM G m) K = A)).card : ℝ)) *
      Sharpness.weight G β J (Sharpness.ofEdgeFun G m)


end Exact3D
end StatMech
