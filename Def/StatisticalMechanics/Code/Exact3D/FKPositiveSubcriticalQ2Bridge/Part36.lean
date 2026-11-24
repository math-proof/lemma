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
public import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part34
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

noncomputable def copyDeleteDecrementEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ)
    (i : Sharpness.FluxEdgeCopy.Copy G m) :
    Sharpness.FluxEdgeCopy.Copy G
        (Function.update m i.1 (m i.1 - 1)) ≃
      {j : Sharpness.FluxEdgeCopy.Copy G m // j ≠ i} where
  toFun := copyDeleteEmbeddingDecrement G m i
  invFun := copyDeletePreimageDecrement G m i
  left_inv := copyDeletePreimageDecrement_embedding_leftInverse G m i
  right_inv := copyDeleteEmbeddingDecrement_preimage_rightInverse G m i


noncomputable def copyDeletePreimageDecrementEraseEmbedding
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ)
    (i : Sharpness.FluxEdgeCopy.Copy G m)
    (K : Finset (Sharpness.FluxEdgeCopy.Copy G m)) :
    {j : Sharpness.FluxEdgeCopy.Copy G m // j ∈ K.erase i} ↪
      Sharpness.FluxEdgeCopy.Copy G
        (Function.update m i.1 (m i.1 - 1)) where
  toFun j :=
    copyDeletePreimageDecrement G m i
      ⟨j.1, (Finset.mem_erase.mp j.2).1⟩
  inj' := by
    intro a b hab
    apply Subtype.ext
    have hsub :
        (⟨a.1, (Finset.mem_erase.mp a.2).1⟩ :
          {j : Sharpness.FluxEdgeCopy.Copy G m // j ≠ i}) =
        ⟨b.1, (Finset.mem_erase.mp b.2).1⟩ := by
      have hmap := congrArg (copyDeleteEmbeddingDecrement G m i) hab
      exact
        (copyDeleteEmbeddingDecrement_preimage_rightInverse G m i _).symm.trans
          (hmap.trans
            (copyDeleteEmbeddingDecrement_preimage_rightInverse G m i _))
    exact congrArg
      (fun z : {j : Sharpness.FluxEdgeCopy.Copy G m // j ≠ i} => z.1)
      hsub


noncomputable def copyDeletePreimageDecrementEraseFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ)
    (i : Sharpness.FluxEdgeCopy.Copy G m)
    (K : Finset (Sharpness.FluxEdgeCopy.Copy G m)) :
    Finset
      (Sharpness.FluxEdgeCopy.Copy G
        (Function.update m i.1 (m i.1 - 1))) :=
  (K.erase i).attach.map (copyDeletePreimageDecrementEraseEmbedding G m i K)


end Exact3D
end StatMech
