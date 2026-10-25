/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWInsetLeftSourceAttachment.Part3
import Def.StatisticalMechanics.Code.Universality.RSWInsetSourceFloor.Part4
open Finset SimpleGraph Set MeasureTheory


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_affineFlipY_lrRestricted (a b c d k : Int) (hcd : c + d = k)
    (L R : Set (Site 2)) (omega : ConfigSpace (Sym2 (Site 2))) :
    omega ∈ rlc_lrRestrictedEvent a b c d L R ->
      rlc_affineFlipYConfig k omega ∈ rlc_lrRestrictedEvent a b c d
        (rlc_affineFlipY k '' L) (rlc_affineFlipY k '' R) := by
  rintro ⟨x, y, hxL, hyR, hxy⟩
  let xf : leftSide a b c d :=
    ⟨rlc_affineFlipY k (x : Site 2),
      (rlc_mem_leftSide_affineFlipY a b c d k hcd x).mp x.2⟩
  let yf : rightSide a b c d :=
    ⟨rlc_affineFlipY k (y : Site 2),
      (rlc_mem_rightSide_affineFlipY a b c d k hcd y).mp y.2⟩
  refine ⟨xf, yf, ⟨x, hxL, rfl⟩, ⟨y, hyR, rfl⟩, ?_⟩
  exact hxy.map (rlc_affineFlipYInducedHom a b c d k hcd omega)

theorem rlc_affineFlipY_image_image (k : Int) (L : Set (Site 2)) :
    rlc_affineFlipY k '' (rlc_affineFlipY k '' L) = L := by
  ext x
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, hzx⟩
    have hzx' : z = x := by simpa using hzx
    rwa [hzx'] at hz
  · intro hx
    exact ⟨rlc_affineFlipY k x,
      ⟨x, hx, rfl⟩, rlc_affineFlipY_involutive k x⟩

theorem rlc_affineFlipY_lrRestricted_prob_eq (a b c d k : Int)
    (hcd : c + d = k) (L R : Set (Site 2)) (p : NNReal) (hp : p <= 1) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real
        (rlc_lrRestrictedEvent a b c d L R) =
      (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real
        (rlc_lrRestrictedEvent a b c d
          (rlc_affineFlipY k '' L) (rlc_affineFlipY k '' R)) := by
  let mu := bernoulliProductMeasure (E := Sym2 (Site 2)) p hp
  have hpre : rlc_affineFlipYConfig k ⁻¹' rlc_lrRestrictedEvent a b c d L R =
      rlc_lrRestrictedEvent a b c d
        (rlc_affineFlipY k '' L) (rlc_affineFlipY k '' R) := by
    ext omega
    constructor
    · intro h
      have ht := rlc_affineFlipY_lrRestricted a b c d k hcd L R
        (rlc_affineFlipYConfig k omega) h
      rwa [rlc_affineFlipYConfig_involutive] at ht
    · intro h
      have ht := rlc_affineFlipY_lrRestricted a b c d k hcd
        (rlc_affineFlipY k '' L) (rlc_affineFlipY k '' R) omega h
      simpa only [rlc_affineFlipY_image_image] using ht
  calc
    mu.real (rlc_lrRestrictedEvent a b c d L R) =
        mu.real (rlc_affineFlipYConfig k ⁻¹'
          rlc_lrRestrictedEvent a b c d L R) :=
      ((rlc_affineFlipY_measurePreserving k p hp).measureReal_preimage
        (measurableSet_of_dependsOn
          (rlc_lrRestrictedEvent_dependsOn a b c d L R)).nullMeasurableSet).symm
    _ = mu.real (rlc_lrRestrictedEvent a b c d
          (rlc_affineFlipY k '' L) (rlc_affineFlipY k '' R)) := by rw [hpre]

theorem rlc_affineFlipY_image_univ (k : Int) :
    rlc_affineFlipY k '' (Set.univ : Set (Site 2)) = Set.univ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨rlc_affineFlipY k x, Set.mem_univ _,
      rlc_affineFlipY_involutive k x⟩

theorem rlc_negOneFlip_image_upper :
    rlc_affineFlipY (-1) '' rlc_upperHalf = rlc_strictLowerHalf := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change 0 <= y 1 at hy
    change -1 - y 1 < 0
    omega
  · intro hx
    change x 1 < 0 at hx
    refine ⟨rlc_affineFlipY (-1) x, ?_, rlc_affineFlipY_involutive (-1) x⟩
    change 0 <= -1 - x 1
    omega

theorem rlc_negOneFlip_image_strictLower :
    rlc_affineFlipY (-1) '' rlc_strictLowerHalf = rlc_upperHalf := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change y 1 < 0 at hy
    change 0 <= -1 - y 1
    omega
  · intro hx
    change 0 <= x 1 at hx
    refine ⟨rlc_affineFlipY (-1) x, ?_, rlc_affineFlipY_involutive (-1) x⟩
    change -1 - x 1 < 0
    omega

theorem rlc_oneFlip_image_strictUpper :
    rlc_affineFlipY 1 '' rlc_strictUpperHalf = rlc_lowerHalf := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change 0 < y 1 at hy
    change 1 - y 1 <= 0
    omega
  · intro hx
    change x 1 <= 0 at hx
    refine ⟨rlc_affineFlipY 1 x, ?_, rlc_affineFlipY_involutive 1 x⟩
    change 0 < 1 - x 1
    omega

theorem rlc_oneFlip_image_lower :
    rlc_affineFlipY 1 '' rlc_lowerHalf = rlc_strictUpperHalf := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change y 1 <= 0 at hy
    change 0 < 1 - y 1
    omega
  · intro hx
    change 0 < x 1 at hx
    refine ⟨rlc_affineFlipY 1 x, ?_, rlc_affineFlipY_involutive 1 x⟩
    change 1 - x 1 <= 0
    omega


theorem rlc_lrRestricted_of_three (a b c d : Int) (hab : a < b) (hcd : c < d)
    (L R : Set (Site 2)) :
    rlc_lrRestrictedEvent a b c d Set.univ R ∩
        rlc_lrRestrictedEvent a b c d L Set.univ ∩
        verticalCrossingEvent a b c d ⊆
      rlc_lrRestrictedEvent a b c d L R := by
  intro omega homega
  obtain ⟨⟨hupper, hlower⟩, hvertical⟩ := homega
  obtain ⟨xu, yu, _hxu, hyu, hcu⟩ := hupper
  obtain ⟨xl, yl, hxl, _hyl, hcl⟩ := hlower
  obtain ⟨xb, yt, hcv⟩ := hvertical
  have hsep : vsFix_VSeparatesHFixed omega a b a b c d :=
    vsFix_arc_sides_imp omega a b a b c d
      (StatMech.Lattice.jec_vsFix_arc_sides omega hab hcd.le)
  have hmeet : HVMeetProperty omega a b a b c d :=
    vsFix_hvMeet omega a b a b c d hsep
  obtain ⟨zu, _hzuO, hzuH, hcuzu, hcvzu⟩ :=
    hmeet (le_refl a) hab.le (le_refl b) xu yu hcu xb yt hcv
  obtain ⟨zl, _hzlO, hzlH, hclzl, hcvzl⟩ :=
    hmeet (le_refl a) hab.le (le_refl b) xl yl hcl xb yt hcv
  have hzlzu : ConnectedWithin 2 omega (rect a b c d)
      ⟨zl, hzlH⟩ ⟨zu, hzuH⟩ := by
    simpa only using hcvzl.symm.trans hcvzu
  have hconn : ConnectedWithin 2 omega (rect a b c d)
      ⟨(xl : Site 2), leftSide_subset xl.2⟩
      ⟨(yu : Site 2), rightSide_subset yu.2⟩ :=
    hclzl.trans (hzlzu.trans (hcuzu.symm.trans hcu))
  exact ⟨xl, yu, hxl, hyu, hconn⟩

theorem rlc_half_localization_of_reflected_union
    (H A A' : Set (ConfigSpace (Sym2 (Site 2)))) (alpha : Real)
    (hcross : alpha <= rba_selfDualMeasure.real H)
    (hsub : H ⊆ A ∪ A')
    (heq : rba_selfDualMeasure.real A = rba_selfDualMeasure.real A') :
    alpha / 2 <= rba_selfDualMeasure.real A := by
  have hmono : rba_selfDualMeasure.real H <=
      rba_selfDualMeasure.real (A ∪ A') :=
    measureReal_mono hsub (measure_ne_top _ _)
  have hunion := measureReal_union_le (μ := rba_selfDualMeasure) A A'
  rw [← heq] at hunion
  linarith


end
end StatMech.Universality
