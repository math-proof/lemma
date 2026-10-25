/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSpinReflection.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusSiteReflection.Part6
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

theorem isingTorusStrictLowerField_reflect
    (i : Fin d)
    (lower : ConfigSpace (IsingTorusStrictLower (k := k) i)) :
    isingTorusSiteReflectField i (isingTorusStrictLowerField i lower) =
      isingTorusStrictUpperField i lower := rfl

theorem isingTorusSitePlaneField_reflect
    (i : Fin d)
    (boundary : ConfigSpace (IsingTorusSitePlane (k := k) i)) :
    isingTorusSiteReflectField i (isingTorusSitePlaneField i boundary) =
      isingTorusSitePlaneField i boundary := by
  funext x
  unfold isingTorusSiteReflectField isingTorusSitePlaneField
  by_cases hp : isingTorusOnSitePlane i x
  · have href := isingTorusSiteReflect_fixed i hp
    simp [href, hp]
  · have hpR := isingTorusSiteReflect_not_plane i hp
    simp [hp, hpR]

theorem isingTorusStrictLower_upper_cross_zero
    (i : Fin d)
    (lower upper : ConfigSpace (IsingTorusStrictLower (k := k) i)) :
    isingTorusDirichletBilinear
        (isingTorusStrictLowerField i lower)
        (isingTorusStrictUpperField i upper) = 0 := by
  unfold isingTorusDirichletBilinear
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro j _
  have hsep := isingTorus_no_edge_meets_both_strict_halves i j x
  push Not at hsep
  by_cases hL : isingTorusInStrictLower i x ∨
      isingTorusInStrictLower i (x + isingTorusStep j)
  · have hU := hsep hL
    rcases hU with ⟨hxU, hyU⟩
    simp [isingTorusStrictUpperField, isingTorusSiteReflectField,
      isingTorusStrictLowerField, hxU, hyU]
  · push Not at hL
    rcases hL with ⟨hxL, hyL⟩
    simp [isingTorusStrictLowerField, hxL, hyL]

theorem isingTorusSpinSiteGlue_eq_fields
    (i : Fin d)
    (boundary : ConfigSpace (IsingTorusSitePlane (k := k) i))
    (lower upper : ConfigSpace (IsingTorusStrictLower (k := k) i)) :
    isingTorusSpinField (isingTorusSiteGlue i boundary lower upper) =
      isingTorusSitePlaneField i boundary +
        isingTorusStrictLowerField i lower +
          isingTorusStrictUpperField i upper := by
  funext x
  change spin (isingTorusSiteGlue i boundary lower upper) x = _
  by_cases hp : isingTorusOnSitePlane i x
  · have href := isingTorusSiteReflect_fixed i hp
    have hnl : ¬ isingTorusInStrictLower i x := by
      unfold isingTorusOnSitePlane at hp
      unfold isingTorusInStrictLower
      rcases hp with hp | hp <;> omega
    have hspin : spin (isingTorusSiteGlue i boundary lower upper) x =
        spin boundary ⟨x, hp⟩ := by
      unfold spin
      simp [isingTorusSiteGlue, hp]
    rw [hspin]
    simp [isingTorusSpinField, isingTorusSiteGlue,
      isingTorusSitePlaneField, isingTorusStrictLowerField,
      isingTorusStrictUpperField, isingTorusSiteReflectField,
      hp, hnl, href]
  · by_cases hl : isingTorusInStrictLower i x
    · have hrl : ¬ isingTorusInStrictLower i
          (isingTorusSiteReflect i x) := by
        rw [isingTorusSiteReflect_strictLower_iff_upper]
        exact (not_lt_of_ge hl.2.le)
      have hspin : spin (isingTorusSiteGlue i boundary lower upper) x =
          spin lower ⟨x, hl⟩ := by
        unfold spin
        simp [isingTorusSiteGlue, hp, hl]
      rw [hspin]
      simp [isingTorusSpinField, isingTorusSiteGlue,
        isingTorusSitePlaneField, isingTorusStrictLowerField,
        isingTorusStrictUpperField, isingTorusSiteReflectField,
        hp, hl, hrl]
    · have hrl := isingTorusSiteReflect_strictLower_of_upper i hp hl
      have hspin : spin (isingTorusSiteGlue i boundary lower upper) x =
          spin upper ⟨isingTorusSiteReflect i x, hrl⟩ := by
        unfold spin
        simp [isingTorusSiteGlue, hp, hl]
      rw [hspin]
      simp [isingTorusSpinField, isingTorusSiteGlue,
        isingTorusSitePlaneField, isingTorusStrictLowerField,
        isingTorusStrictUpperField, isingTorusSiteReflectField,
        hp, hl, hrl]

theorem isingTorusStrictUpper_dirichlet
    (i : Fin d)
    (lower : ConfigSpace (IsingTorusStrictLower (k := k) i)) :
    isingTorusDirichlet (isingTorusStrictUpperField i lower) =
      isingTorusDirichlet (isingTorusStrictLowerField i lower) := by
  rw [← isingTorusStrictLowerField_reflect,
    isingTorusDirichlet_siteReflectField]

theorem isingTorusSitePlane_upper_bilinear
    (i : Fin d)
    (boundary : ConfigSpace (IsingTorusSitePlane (k := k) i))
    (lower : ConfigSpace (IsingTorusStrictLower (k := k) i)) :
    isingTorusDirichletBilinear
        (isingTorusSitePlaneField i boundary)
        (isingTorusStrictUpperField i lower) =
      isingTorusDirichletBilinear
        (isingTorusSitePlaneField i boundary)
        (isingTorusStrictLowerField i lower) := by
  have h := isingTorusDirichletBilinear_siteReflectField i
    (isingTorusSitePlaneField i boundary)
    (isingTorusStrictLowerField i lower)
  rw [isingTorusSitePlaneField_reflect,
    isingTorusStrictLowerField_reflect] at h
  exact h

theorem isingTorusSiteGlue_dirichlet_midpoint
    (i : Fin d)
    (boundary : ConfigSpace (IsingTorusSitePlane (k := k) i))
    (lower upper : ConfigSpace (IsingTorusStrictLower (k := k) i)) :
    2 * isingTorusDirichlet
        (isingTorusSpinField (isingTorusSiteGlue i boundary lower upper)) =
      isingTorusDirichlet
          (isingTorusSpinField (isingTorusSiteGlue i boundary lower lower)) +
        isingTorusDirichlet
          (isingTorusSpinField (isingTorusSiteGlue i boundary upper upper)) := by
  let B := isingTorusSitePlaneField i boundary
  let L := fun sigma : ConfigSpace (IsingTorusStrictLower (k := k) i) =>
    isingTorusStrictLowerField i sigma
  let U := fun sigma : ConfigSpace (IsingTorusStrictLower (k := k) i) =>
    isingTorusStrictUpperField i sigma
  rw [isingTorusSpinSiteGlue_eq_fields,
    isingTorusSpinSiteGlue_eq_fields,
    isingTorusSpinSiteGlue_eq_fields]
  change 2 * isingTorusDirichlet (B + L lower + U upper) =
    isingTorusDirichlet (B + L lower + U lower) +
      isingTorusDirichlet (B + L upper + U upper)
  rw [isingTorusDirichlet_add (B + L lower) (U upper),
    isingTorusDirichlet_add B (L lower),
    isingTorusDirichlet_add (B + L lower) (U lower),
    isingTorusDirichlet_add B (L lower),
    isingTorusDirichlet_add (B + L upper) (U upper),
    isingTorusDirichlet_add B (L upper)]
  rw [isingTorusDirichletBilinear_add_left B (L lower) (U upper),
    isingTorusDirichletBilinear_add_left B (L lower) (U lower),
    isingTorusDirichletBilinear_add_left B (L upper) (U upper)]
  have hcrossLU := isingTorusStrictLower_upper_cross_zero i lower upper
  have hcrossLL := isingTorusStrictLower_upper_cross_zero i lower lower
  have hcrossUU := isingTorusStrictLower_upper_cross_zero i upper upper
  have hDUl := isingTorusStrictUpper_dirichlet i lower
  have hDUu := isingTorusStrictUpper_dirichlet i upper
  have hBUl := isingTorusSitePlane_upper_bilinear i boundary lower
  have hBUu := isingTorusSitePlane_upper_bilinear i boundary upper
  change isingTorusDirichletBilinear (L lower) (U upper) = 0 at hcrossLU
  change isingTorusDirichletBilinear (L lower) (U lower) = 0 at hcrossLL
  change isingTorusDirichletBilinear (L upper) (U upper) = 0 at hcrossUU
  change isingTorusDirichlet (U lower) = isingTorusDirichlet (L lower) at hDUl
  change isingTorusDirichlet (U upper) = isingTorusDirichlet (L upper) at hDUu
  change isingTorusDirichletBilinear B (U lower) =
    isingTorusDirichletBilinear B (L lower) at hBUl
  change isingTorusDirichletBilinear B (U upper) =
    isingTorusDirichletBilinear B (L upper) at hBUu
  rw [hcrossLU, hcrossLL, hcrossUU, hDUl, hDUu, hBUl, hBUu]
  ring

end StatMech.FrontierA
