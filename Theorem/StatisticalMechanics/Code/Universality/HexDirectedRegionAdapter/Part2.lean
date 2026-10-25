/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexDirectedRegionAdapter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part3
import Def.StatisticalMechanics.Code.Universality.HexDirectedRegionAdapter.Part2


namespace StatMech.Universality

open Complex HexWalk


theorem hexStripDirMids_fst_mem_midsAux
    (m : ℂ) (h : ℤ) (ts : List ℤ) (p : ℂ × ℤ)
    (hp : p ∈ hexStripDirMids m h ts) : p.1 ∈ midsAux m h ts := by
  induction ts generalizing m h with
  | nil =>
      simp only [hexStripDirMids_nil, List.mem_singleton] at hp
      subst p
      simp [midsAux]
  | cons t ts ih =>
      rw [hexStripDirMids_cons, List.mem_cons] at hp
      rw [midsAux_cons, List.mem_cons]
      rcases hp with rfl | hp
      · exact Or.inl rfl
      · exact Or.inr
          (ih (m + halfStep h + halfStep (h + t)) (h + t) hp)


theorem hexStripMembershipDRegion_staysInDir
    (M : Finset ℂ) (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hstay : (ofTurns a h0 ts).StaysIn (fun m => m ∈ M)) :
    hexStripStaysInDir (hexStripMembershipDRegion M) a h0 ts := by
  intro p hp
  apply hstay p.1
  exact hexStripDirMids_fst_mem_midsAux a h0 ts p hp


theorem hexStripMembershipDRegion_headingPeriodic (M : Finset ℂ) :
    HexHeadingPeriodic (hexStripMembershipDRegion M) := by
  intro m h hm
  exact hm


theorem hexStripMembershipDRegion_not_uniqueInterior
    (M : Finset ℂ) (a : ℂ) (ha : a ∈ M) (h0 : ℤ) :
    ¬(∀ h : ℤ,
      hexStripInterior (hexStripMembershipDRegion M) (a + halfStep h) →
        halfStep h = halfStep h0) :=
  not_hexStrip_uniqueInterior_of_headingPeriodic_start
    (hexStripMembershipDRegion M) a h0
    (hexStripMembershipDRegion_headingPeriodic M) ha


theorem hexReturning_staysInDir_of_launch
    (dregion : ℂ → ℤ → Prop) (a : ℂ) (h0 : ℤ)
    (hlaunch : dregion a h0) (ts : List ℤ)
    (hlegal : (ofTurns a h0 ts).IsLegalSAW)
    (hend : (ofTurns a h0 ts).EndsAt a) :
    hexStripStaysInDir dregion a h0 ts := by
  have hnil := hexReturningLegalSAW_eq_nil a h0 ts hlegal hend
  rw [hnil]
  intro p hp
  simp only [hexStripDirMids_nil, List.mem_singleton] at hp
  subst p
  exact hlaunch


end StatMech.Universality
