/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareCoverIntersection.Part7
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusDisjointWinding.Part2
open SimpleGraph


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

theorem fkRectNatScale_squareDeckTranslation
    (R : FKRectTorus) (n : Nat) (u : Int × Int) :
    fkRectNatScale n (fkRectSquareDeckTranslation R u) =
      fkRectSquareDeckTranslation R
        ((n : Int) * u.1, (n : Int) * u.2) := by
  apply Prod.ext <;>
    simp [fkRectNatScale, fkRectSquareDeckTranslation] <;> ring

theorem fkRectSquareRepresentativeVertex_dartTranslate_deck
    (R : FKRectTorus) (u : Int × Int)
    (d : FKRectIntegralSquareDart) :
    fkRectSquareRepresentativeVertex R
        (fkRectIntegralSquareDartTranslate
          (fkRectSquareDeckTranslation R u) d).1 =
      fkRectSquareRepresentativeVertex R d.1 := by
  exact fkRectSquareRepresentativeVertex_add_deck R d.1 u

theorem fkRectSquareRepresentativeVertex_dartTranslateEnd_deck
    (R : FKRectTorus) (u : Int × Int)
    (d : FKRectIntegralSquareDart) :
    fkRectSquareRepresentativeVertex R
        (fkRectIntegralSquareDartEnd
          (fkRectIntegralSquareDartTranslate
            (fkRectSquareDeckTranslation R u) d)) =
      fkRectSquareRepresentativeVertex R
        (fkRectIntegralSquareDartEnd d) := by
  rw [fkRectIntegralSquareDartEnd_translate]
  convert fkRectSquareRepresentativeVertex_add_deck R
    (fkRectIntegralSquareDartEnd d) u using 1


theorem FKRectIntegralDartListSupportedOn.repeatTranslated_deck
    (R : FKRectTorus) {l : List FKRectIntegralSquareDart}
    {S : R.Vertex → Prop} (u : Int × Int)
    (h : FKRectIntegralDartListSupportedOn R l S) (n : Nat) :
    FKRectIntegralDartListSupportedOn R
      (fkRectRepeatTranslatedDartPath l
        (fkRectSquareDeckTranslation R u) n) S := by
  induction n with
  | zero =>
      simp [FKRectIntegralDartListSupportedOn,
        fkRectRepeatTranslatedDartPath]
  | succ n ih =>
      intro d hd
      rw [fkRectRepeatTranslatedDartPath, List.mem_append] at hd
      rcases hd with hd | hd
      · exact ih d hd
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
        rw [fkRectNatScale_squareDeckTranslation]
        constructor
        · rw [fkRectSquareRepresentativeVertex_dartTranslate_deck]
          exact (h a ha).1
        · rw [fkRectSquareRepresentativeVertex_dartTranslateEnd_deck]
          exact (h a ha).2


theorem FKRectIntegralDartListSupportedOn.exists_pointLift
    (R : FKRectTorus) {l : List FKRectIntegralSquareDart}
    {S : R.Vertex → Prop}
    (h : FKRectIntegralDartListSupportedOn R l S)
    {p : ZMod (fkRectSquareCoverSide R) ×
      ZMod (fkRectSquareCoverSide R)}
    (hp : FKRectDartListUsesPoint
      (l.map (fkRectIntegralSquareDartMod (fkRectSquareCoverSide R))) p) :
    ∃ z : Int × Int,
      fkRectIntegralSquarePointMod (fkRectSquareCoverSide R) z = p ∧
      S (fkRectSquareRepresentativeVertex R z) := by
  obtain ⟨dmod, hdmod, hstart | hend⟩ := hp
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hdmod
    exact ⟨d.1, hstart, (h d hd).1⟩
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hdmod
    refine ⟨fkRectIntegralSquareDartEnd d, ?_, (h d hd).2⟩
    rw [fkRectIntegralSquareDartMod_end] at hend
    exact hend


theorem fkRectDartListUsesPoint_disjoint_of_supported
    (R : FKRectTorus) {l k : List FKRectIntegralSquareDart}
    {S T : R.Vertex → Prop}
    (hl : FKRectIntegralDartListSupportedOn R l S)
    (hk : FKRectIntegralDartListSupportedOn R k T)
    (hST : ∀ x, S x → ¬ T x) :
    ∀ p,
      FKRectDartListUsesPoint
          (l.map (fkRectIntegralSquareDartMod
            (fkRectSquareCoverSide R))) p →
        ¬ FKRectDartListUsesPoint
          (k.map (fkRectIntegralSquareDartMod
            (fkRectSquareCoverSide R))) p := by
  intro p hp hq
  obtain ⟨a, ha, hSa⟩ := hl.exists_pointLift R hp
  obtain ⟨b, hb, hTb⟩ := hk.exists_pointLift R hq
  have hab : fkRectSquareRepresentativeVertex R a =
      fkRectSquareRepresentativeVertex R b := by
    apply fkRectSquareRepresentativeVertex_eq_of_pointMod_eq R
    rw [ha, hb]
  exact hST _ hSa (hab ▸ hTb)


end
end StatMech.FrontierD
