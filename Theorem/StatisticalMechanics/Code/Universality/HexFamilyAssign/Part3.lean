/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFamilyAssign.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexContourDecomp.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Def.StatisticalMechanics.Code.Universality.HexFamilyAssign.Part2


namespace StatMech.Universality

open Complex

open scoped BigOperators


theorem hexCell_geom (c : ℂ) (v : Fin 1) (j : Fin 3) :
    (hexCell c).mid v j - (hexCell c).pos v = (1 / 2 : ℂ) * hexUnit (2 * (j : ℤ)) := by
  simp only [hexCell, sub_zero]


theorem hexCell_straightSide (c : ℂ) (j0 : Fin 3) (s : Finset (HexIncidence (Fin 1)))
    (hconst : ∀ e ∈ s, e.edge = j0) :
    ∀ e ∈ s, (hexCell c).mid e.vtx e.edge - (hexCell c).pos e.vtx
      = (1 / 2 : ℂ) * hexUnit (2 * (j0 : ℤ)) := by
  refine hexFam_straightSide_dir (hexCell c) (fun _ j => 2 * (j : ℤ)) (hexCell_geom c) s
    (2 * (j0 : ℤ)) ?_
  intro e he
  rw [hconst e he]


theorem hexBoundary_identity_via_family {V : Type*} [DecidableEq V]
    (D : HexDomain V) (P : D.InteriorPairing) (hsub : P.interior ⊆ D.incidences)
    (F : HexFamilyData D P) (hFa : F.Fa = 1) :
    hexBdryCl * F.lam + hexBdryCt * (F.taup + F.taum) + F.ups = 1 := by
  have h := hexBoundary_identity_via_decomp D P hsub F.toDecomp (by simpa using hFa)
  simpa using h


theorem hexBoundary_identity_scales_via_family {V : Type*} [DecidableEq V]
    (D : ℕ → HexDomain V) (P : ∀ v, (D v).InteriorPairing)
    (hsub : ∀ v, (P v).interior ⊆ (D v).incidences)
    (F : ∀ v, HexFamilyData (D v) (P v))
    (hFa : ∀ v, 1 ≤ v → (F v).Fa = 1) :
    ∀ v, 1 ≤ v →
      hexBdryCl * (F v).lam + hexBdryCt * ((F v).taup + (F v).taum) + (F v).ups = 1 := by
  intro v hv
  exact hexBoundary_identity_via_family (D v) (P v) (hsub v) (F v) (hFa v hv)

end StatMech.Universality
