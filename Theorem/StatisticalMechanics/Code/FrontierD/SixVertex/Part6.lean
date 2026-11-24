module
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Order.Hom.PowersetCard
public import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part7
open Finset Matrix


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertex.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

theorem sixVertexSectorTransfer_isHermitian (N n : ℕ) (c : ℝ) :
    (sixVertexSectorTransfer N n c).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro x y
  simp only [star_id_of_comm]
  exact sixVertexTransfer_symmetric N c (sixVertexSectorRow y) (sixVertexSectorRow x)


theorem sixVertexSector_nonempty {N n : ℕ} (hn : n ≤ N) :
    Nonempty (SixVertexSector N n) := by
  let x : Finset (Fin N) := {i | i.val < n}
  have hcard : #{i : Fin N | i.val < n} = n := by
    rw [Fin.card_filter_val_lt, min_eq_right hn]
  exact ⟨⟨x, hcard⟩⟩


end StatMech.FrontierD
