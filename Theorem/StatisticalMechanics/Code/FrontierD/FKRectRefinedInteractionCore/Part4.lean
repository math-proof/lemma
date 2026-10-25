/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedInteractionCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedBoundary.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectRefinedInteractionCore.Part3
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

open IntegralSquareTorusCycle

noncomputable section

variable {L : Nat} [Fact (8 < L)]

theorem pointMass_translate
    (u a p : ZMod L × ZMod L) :
    pointMass (fkRectRefinedPointTranslate u a)
        (fkRectRefinedPointTranslate u p) = pointMass a p := by
  unfold pointMass fkRectRefinedPointTranslate
  congr 1
  apply propext
  simp only [Prod.ext_iff]
  constructor <;> rintro ⟨h1, h2⟩
  · exact ⟨add_right_cancel h1, add_right_cancel h2⟩
  · exact ⟨congrArg (fun z => z + u.1) h1,
      congrArg (fun z => z + u.2) h2⟩

theorem dartHorizontal_translate
    (u p : ZMod L × ZMod L) (d : ons_Dart L) :
    dartHorizontal (fkRectRefinedDartTranslateMod u d)
        (fkRectRefinedPointTranslate u p) = dartHorizontal d p := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu
  · change pointMass (fkRectRefinedPointTranslate u (x, y))
        (fkRectRefinedPointTranslate u p) = pointMass (x, y) p
    exact pointMass_translate u (x, y) p
  · simp [dartHorizontal, fkRectRefinedDartTranslateMod]
  · change -pointMass (x + u.1 - 1, y + u.2)
        (fkRectRefinedPointTranslate u p) = -pointMass (x - 1, y) p
    rw [show (x + u.1 - 1, y + u.2) =
        fkRectRefinedPointTranslate u (x - 1, y) by
      apply Prod.ext <;> simp [fkRectRefinedPointTranslate] <;> ring,
      pointMass_translate]
  · simp [dartHorizontal, fkRectRefinedDartTranslateMod]

theorem dartVertical_translate
    (u p : ZMod L × ZMod L) (d : ons_Dart L) :
    dartVertical (fkRectRefinedDartTranslateMod u d)
        (fkRectRefinedPointTranslate u p) = dartVertical d p := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu
  · simp [dartVertical, fkRectRefinedDartTranslateMod]
  · change pointMass (fkRectRefinedPointTranslate u (x, y))
        (fkRectRefinedPointTranslate u p) = pointMass (x, y) p
    exact pointMass_translate u (x, y) p
  · simp [dartVertical, fkRectRefinedDartTranslateMod]
  · change -pointMass (x + u.1, y + u.2 - 1)
        (fkRectRefinedPointTranslate u p) = -pointMass (x, y - 1) p
    rw [show (x + u.1, y + u.2 - 1) =
        fkRectRefinedPointTranslate u (x, y - 1) by
      apply Prod.ext <;> simp [fkRectRefinedPointTranslate] <;> ring,
      pointMass_translate]


theorem fkRectRefinedRawInteraction_translate
    (u : ZMod L × ZMod L) (a b : List (ons_Dart L)) :
    fkRectRefinedRawInteraction
        (a.map (fkRectRefinedDartTranslateMod u))
        (b.map (fkRectRefinedDartTranslateMod u)) =
      fkRectRefinedRawInteraction a b := by
  classical
  unfold fkRectRefinedRawInteraction
  rw [show (∑ p : ZMod L × ZMod L, _) =
      ∑ p : ZMod L × ZMod L,
        (((a.map (fkRectRefinedDartTranslateMod u)).map
            (fun d => dartHorizontal d
              (fkRectRefinedPointTranslate u p))).sum *
          ((b.map (fkRectRefinedDartTranslateMod u)).map
            (fun d => dartVertical d
              ((fkRectRefinedPointTranslate u p).1,
                (fkRectRefinedPointTranslate u p).2 - 1))).sum -
          ((a.map (fkRectRefinedDartTranslateMod u)).map
            (fun d => dartVertical d
              (fkRectRefinedPointTranslate u p))).sum *
          ((b.map (fkRectRefinedDartTranslateMod u)).map
            (fun d => dartHorizontal d
              ((fkRectRefinedPointTranslate u p).1 - 1,
                (fkRectRefinedPointTranslate u p).2))).sum) by
    simpa [fkRectRefinedPointTranslate] using
      (Equiv.sum_comp
        (Equiv.prodCongr (Equiv.addRight u.1) (Equiv.addRight u.2))
        (fun p : ZMod L × ZMod L =>
          (((a.map (fkRectRefinedDartTranslateMod u)).map
              (fun d => dartHorizontal d p)).sum *
            ((b.map (fkRectRefinedDartTranslateMod u)).map
              (fun d => dartVertical d (p.1, p.2 - 1))).sum -
            ((a.map (fkRectRefinedDartTranslateMod u)).map
              (fun d => dartVertical d p)).sum *
            ((b.map (fkRectRefinedDartTranslateMod u)).map
              (fun d => dartHorizontal d (p.1 - 1, p.2))).sum))).symm]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [List.map_map]
  have hs : ((fkRectRefinedPointTranslate u p).1,
      (fkRectRefinedPointTranslate u p).2 - 1) =
      fkRectRefinedPointTranslate u (p.1, p.2 - 1) := by
    apply Prod.ext <;> simp [fkRectRefinedPointTranslate] <;> ring
  have hw : ((fkRectRefinedPointTranslate u p).1 - 1,
      (fkRectRefinedPointTranslate u p).2) =
      fkRectRefinedPointTranslate u (p.1 - 1, p.2) := by
    apply Prod.ext <;> simp [fkRectRefinedPointTranslate] <;> ring
  rw [hs, hw]
  rw [show (fun d => dartHorizontal d
        (fkRectRefinedPointTranslate u p)) ∘
        fkRectRefinedDartTranslateMod u =
      fun d => dartHorizontal d p from
    funext (fun d => dartHorizontal_translate u p d)]
  rw [show (fun d => dartVertical d
        (fkRectRefinedPointTranslate u (p.1, p.2 - 1))) ∘
        fkRectRefinedDartTranslateMod u =
      fun d => dartVertical d (p.1, p.2 - 1) from
    funext (fun d => dartVertical_translate u (p.1, p.2 - 1) d)]
  rw [show (fun d => dartVertical d
        (fkRectRefinedPointTranslate u p)) ∘
        fkRectRefinedDartTranslateMod u =
      fun d => dartVertical d p from
    funext (fun d => dartVertical_translate u p d)]
  rw [show (fun d => dartHorizontal d
        (fkRectRefinedPointTranslate u (p.1 - 1, p.2))) ∘
        fkRectRefinedDartTranslateMod u =
      fun d => dartHorizontal d (p.1 - 1, p.2) from
    funext (fun d => dartHorizontal_translate u (p.1 - 1, p.2) d)]


theorem fkRectIntegralSquareDartMod_translate
    (u : Int × Int) (d : FKRectIntegralSquareDart) :
    fkRectIntegralSquareDartMod L
        (fkRectIntegralSquareDartTranslate u d) =
      fkRectRefinedDartTranslateMod ((u.1 : ZMod L), (u.2 : ZMod L))
        (fkRectIntegralSquareDartMod L d) := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  apply Prod.ext
  · apply Prod.ext <;>
      simp [fkRectIntegralSquareDartMod,
        fkRectIntegralSquareDartTranslate,
        fkRectRefinedDartTranslateMod, fkRectRefinedPointTranslate]
  · rfl


theorem fkRectRefinedRawInteraction_integralTranslate
    (u : Int × Int)
    (a b : List FKRectIntegralSquareDart) :
    fkRectRefinedRawInteraction
        ((a.map (fkRectIntegralSquareDartTranslate u)).map
          (fkRectIntegralSquareDartMod L))
        ((b.map (fkRectIntegralSquareDartTranslate u)).map
          (fkRectIntegralSquareDartMod L)) =
      fkRectRefinedRawInteraction
        (a.map (fkRectIntegralSquareDartMod L))
        (b.map (fkRectIntegralSquareDartMod L)) := by
  simpa only [List.map_map, Function.comp_def,
    fkRectIntegralSquareDartMod_translate] using
    fkRectRefinedRawInteraction_translate
      (L := L) ((u.1 : ZMod L), (u.2 : ZMod L))
      (a.map (fkRectIntegralSquareDartMod L))
      (b.map (fkRectIntegralSquareDartMod L))

end
end StatMech.FrontierD
