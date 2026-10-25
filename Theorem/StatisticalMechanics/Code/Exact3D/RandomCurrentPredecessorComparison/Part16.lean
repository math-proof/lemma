/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part15
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

theorem edgeCopyCopiesOfEdge_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (i : Sharpness.FluxEdgeCopy.Copy G m) :
    i ∈ edgeCopyCopiesOfEdge G m e0 ↔ i.1 = e0 := by
  simp [edgeCopyCopiesOfEdge]


theorem edgeCopyCopiesOfEdge_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    (edgeCopyCopiesOfEdge G m e0).card = m e0 := by
  classical
  let f :
      {i : Sharpness.FluxEdgeCopy.Copy G m //
        i ∈ edgeCopyCopiesOfEdge G m e0} → Fin (m e0) :=
    fun i =>
      Fin.cast (by rw [(edgeCopyCopiesOfEdge_mem G m e0 i.1).mp i.2])
        i.1.2
  let g :
      Fin (m e0) →
        {i : Sharpness.FluxEdgeCopy.Copy G m //
          i ∈ edgeCopyCopiesOfEdge G m e0} :=
    fun k => ⟨⟨e0, k⟩, by simp [edgeCopyCopiesOfEdge]⟩
  have hfg : Function.LeftInverse g f := by
    intro i
    apply Subtype.ext
    rcases i with ⟨⟨e, k⟩, hi⟩
    have he : e = e0 := (edgeCopyCopiesOfEdge_mem G m e0 ⟨e, k⟩).mp hi
    subst e
    simp [f, g]
  have hgf : Function.RightInverse g f := by
    intro k
    apply Fin.ext
    simp [f, g]
  let e :
      {i : Sharpness.FluxEdgeCopy.Copy G m //
        i ∈ edgeCopyCopiesOfEdge G m e0} ≃ Fin (m e0) :=
    { toFun := f
      invFun := g
      left_inv := hfg
      right_inv := hgf }
  have hcard := Fintype.card_congr e
  simpa using hcard


end Exact3D
end StatMech
