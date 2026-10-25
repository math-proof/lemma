/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualGeometry.Part2
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualEquiv.Part5
open scoped symmDiff
open Finset


namespace StatMech.FrontierA

noncomputable section

theorem mem_cubicalPlaquetteCells_iff_mem_cellFaces
    {a b c : Nat} (q : CubicalCell a b c) (p : CubicalPlaquette a b c) :
    q ∈ cubicalPlaquetteCells p ↔ p ∈ cubicalCellFaces q := by
  rcases q with ⟨i, j, k⟩
  cases p <;>
    simp [cubicalPlaquetteCells, cubicalDualEnds, cubicalCellFaces] <;> tauto

theorem plaquetteIncidenceCount_cellFaces_eq
    {a b c : Nat} (S : Finset (CubicalCell a b c))
    (p : CubicalPlaquette a b c) :
    plaquetteIncidenceCount cubicalCellFaces S p =
      (S.filter fun q => q ∈ cubicalPlaquetteCells p).card := by
  rw [plaquetteIncidenceCount_eq_filter_card]
  congr 1
  ext q
  simp only [mem_filter]
  rw [mem_cubicalPlaquetteCells_iff_mem_cellFaces]


end
end StatMech.FrontierA
