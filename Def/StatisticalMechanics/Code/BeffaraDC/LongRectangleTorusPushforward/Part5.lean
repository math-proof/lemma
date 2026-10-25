/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusCover.Part6
import Theorem.StatisticalMechanics.Code.FK.FKG
import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusPushforward.Part5
open MeasureTheory Set
open scoped ENNReal NNReal


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager

open StatMech.Universality


noncomputable def torusAmbientTranslateEdgeEquiv
    (L : ℕ) [Fact (2 < L)] (t : Site 2) :
    TorusAmbientEdge L ≃ TorusAmbientEdge L where
  toFun e := ⟨Sym2.map (torusSiteTranslateEquiv L t) e.1,
    (torusSiteTranslate_mem_edgeFinset_iff L t e.1).2 e.2⟩
  invFun e := ⟨Sym2.map (torusSiteTranslateEquiv L t).symm e.1, by
    apply (torusSiteTranslate_mem_edgeFinset_iff L t
      (Sym2.map (torusSiteTranslateEquiv L t).symm e.1)).1
    simpa only [Sym2.map_map, Equiv.self_comp_symm, Sym2.map_id', id_eq]
      using e.2⟩
  left_inv e := by
    apply Subtype.ext
    change Sym2.map (torusSiteTranslateEquiv L t).symm
        (Sym2.map (torusSiteTranslateEquiv L t) e.1) = e.1
    rw [Sym2.map_map]
    calc
      Sym2.map ((torusSiteTranslateEquiv L t).symm ∘
          torusSiteTranslateEquiv L t) e.1 =
          Sym2.map (fun x => x) e.1 := by
        apply Sym2.map_congr
        intro x _hx
        exact (torusSiteTranslateEquiv L t).symm_apply_apply x
      _ = e.1 := congrFun Sym2.map_id' e.1
  right_inv e := by
    apply Subtype.ext
    change Sym2.map (torusSiteTranslateEquiv L t)
        (Sym2.map (torusSiteTranslateEquiv L t).symm e.1) = e.1
    rw [Sym2.map_map]
    calc
      Sym2.map (torusSiteTranslateEquiv L t ∘
          (torusSiteTranslateEquiv L t).symm) e.1 =
          Sym2.map (fun x => x) e.1 := by
        apply Sym2.map_congr
        intro x _hx
        exact (torusSiteTranslateEquiv L t).apply_symm_apply x
      _ = e.1 := congrFun Sym2.map_id' e.1


noncomputable def torusAmbientTranslateConfig
    (L : ℕ) [Fact (2 < L)] (t : Site 2)
    (omega : TorusAmbientConfig L) : TorusAmbientConfig L :=
  fun e => omega (torusAmbientTranslateEdgeEquiv L t e)


noncomputable def torusAmbientTranslateConfigEquiv
    (L : ℕ) [Fact (2 < L)] (t : Site 2) :
    TorusAmbientConfig L ≃ TorusAmbientConfig L where
  toFun := torusAmbientTranslateConfig L t
  invFun eta := fun e => eta ((torusAmbientTranslateEdgeEquiv L t).symm e)
  left_inv omega := by
    funext e
    simp [torusAmbientTranslateConfig]
  right_inv eta := by
    funext e
    simp [torusAmbientTranslateConfig]


end StatMech.BeffaraDC
