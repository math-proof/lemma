/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialPrimalLabel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleCount


namespace StatMech.FrontierD

@[simp] theorem fkRectMedialVertexOfEdge_fst_val
    (R : FKRectTorus) (e : R.EdgeIndex) :
    (fkRectMedialVertexOfEdge R e).1.val =
      e.1.toNat + 2 * e.2.1.val := by
  rcases e with ⟨b, x, y⟩
  cases b <;> rfl

@[simp] theorem fkRectMedialVertexOfEdge_snd
    (R : FKRectTorus) (e : R.EdgeIndex) :
    (fkRectMedialVertexOfEdge R e).2 = e.2.2 := by
  rcases e with ⟨b, x, y⟩
  cases b <;> rfl

@[simp] theorem fkRectTorusMedialEdgeEquiv_symm_fst_val
    (R : FKRectTorus) (e : R.EdgeIndex) :
    ((fkRectTorusMedialEdgeEquiv R).symm e).1.val =
      e.1.toNat + 2 * e.2.1.val :=
  fkRectMedialVertexOfEdge_fst_val R e

@[simp] theorem fkRectTorusMedialEdgeEquiv_symm_snd
    (R : FKRectTorus) (e : R.EdgeIndex) :
    ((fkRectTorusMedialEdgeEquiv R).symm e).2 = e.2.2 :=
  fkRectMedialVertexOfEdge_snd R e


end StatMech.FrontierD
