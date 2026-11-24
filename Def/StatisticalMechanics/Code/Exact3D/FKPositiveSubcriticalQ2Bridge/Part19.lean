module
public import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
public import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
public import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
public import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
public import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
public import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
public import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
public import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
public import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
public import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
public import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
public import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
public import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
public import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
public import Abbrev.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

noncomputable def edgeCopySourcePairDataWeight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) {A B : Finset V}
    (d : edgeCopySourcePairData G A B) : ℝ :=
  Sharpness.weight G β J (Sharpness.ofEdgeFun G d.1)


noncomputable def edgeCopySourcePairSummand
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V)
    (m : ↥G.edgeFinset → ℕ) : ℝ :=
  (∑ S : Finset (Sharpness.FluxEdgeCopy.Copy G m),
    (if Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m) S = A then
      (1 : ℝ)
    else
      0) *
    (if Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m)
          ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) \ S) = B then
      (1 : ℝ)
    else
      0)) *
  Sharpness.weight G β J (Sharpness.ofEdgeFun G m)


end Exact3D
end StatMech
