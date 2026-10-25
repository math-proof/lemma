/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCrossingFromArms
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCrosscut
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCluster.Part8
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneJoinedArmsHighProbability.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneTranslation.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRotated
import Mathlib.Topology.Subpath
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCage.Part3
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

namespace ContinuousHalfPlaneCrosscut

theorem rectangleMargin_nonneg_iff (a b c d : Real) (z : Fin 2 → Real) :
    0 ≤ rectangleMargin a b c d z ↔
      ContinuousRectangleCrossing.InRectangle a b c d z := by
  simp only [rectangleMargin, le_min_iff,
    ContinuousRectangleCrossing.InRectangle]
  constructor
  · rintro ⟨hxa, hbx, hyc, hdy⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨hax, hxb, hcy, hyd⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩


theorem exists_first_rectangle_exit_prefix
    {start finish : Fin 2 → Real} (gamma : Path start finish)
    {a b c d : Real}
    (hstart : a < start 0 ∧ start 0 < b ∧
      c < start 1 ∧ start 1 < d)
    (hfinish : ¬ ContinuousRectangleCrossing.InRectangle a b c d finish) :
    ∃ t : unitInterval,
      rectangleMargin a b c d (gamma t) = 0 ∧
      Set.range (gamma.subpath 0 t) ⊆
        {z | ContinuousRectangleCrossing.InRectangle a b c d z} ∧
      Set.range (gamma.subpath 0 t) ⊆ Set.range gamma ∧
      (gamma t 0 = a ∨ gamma t 0 = b ∨
        gamma t 1 = c ∨ gamma t 1 = d) := by
  let f : unitInterval → Real := fun u =>
    rectangleMargin a b c d (gamma u)
  have hf : Continuous f := by
    dsimp only [f, rectangleMargin]
    fun_prop
  have hf0 : 0 < f 0 := by
    dsimp only [f, rectangleMargin]
    simp only [Path.source]
    apply lt_min
    · linarith [hstart.1]
    apply lt_min
    · linarith [hstart.2.1]
    apply lt_min <;> linarith [hstart.2.2.1, hstart.2.2.2]
  have hf1 : f 1 < 0 := by
    apply lt_of_not_ge
    intro hnonneg
    apply hfinish
    apply (rectangleMargin_nonneg_iff a b c d finish).1
    simpa only [f, Path.target] using hnonneg
  have hzero : ∃ u : unitInterval, f u = 0 := by
    have hz : (0 : Real) ∈ Set.Icc (f 1) (f 0) := ⟨hf1.le, hf0.le⟩
    obtain ⟨u, _hu, hu0⟩ :=
      intermediate_value_Icc' (show (0 : unitInterval) ≤ 1 by simp)
        hf.continuousOn hz
    exact ⟨u, hu0⟩
  let K : Set unitInterval := {u | f u = 0}
  have hKclosed : IsClosed K := isClosed_eq hf continuous_const
  have hKne : K.Nonempty := by
    obtain ⟨u, hu⟩ := hzero
    exact ⟨u, hu⟩
  obtain ⟨t, htK, htmin⟩ := hKclosed.isCompact.exists_isMinOn
    hKne continuous_id.continuousOn
  change f t = 0 at htK
  have hprefixNonneg : ∀ u : unitInterval, u ≤ t → 0 ≤ f u := by
    intro u hut
    by_contra hnot
    have hfu : f u < 0 := lt_of_not_ge hnot
    have huPos : (0 : unitInterval) < u := by
      by_contra hu0
      have : u = 0 := le_antisymm (le_of_not_gt hu0) u.2.1
      subst u
      exact (not_lt_of_ge hf0.le) hfu
    have hz : (0 : Real) ∈ Set.Icc (f u) (f 0) := ⟨hfu.le, hf0.le⟩
    obtain ⟨v, hvI, hv0⟩ :=
      intermediate_value_Icc' (show (0 : unitInterval) ≤ u by exact u.2.1)
        hf.continuousOn hz
    have hvlt : v < t := by
      have hvle : v ≤ u := hvI.2
      have hutNe : u ≠ t := by
        intro hutEq
        subst u
        rw [htK] at hfu
        exact lt_irrefl _ hfu
      exact lt_of_le_of_lt hvle (lt_of_le_of_ne hut hutNe)
    exact (not_lt_of_ge (htmin hv0)) hvlt
  have htRect : ContinuousRectangleCrossing.InRectangle a b c d (gamma t) :=
    (rectangleMargin_nonneg_iff a b c d (gamma t)).1
      (by change 0 ≤ f t; rw [htK])
  have htSide : gamma t 0 = a ∨ gamma t 0 = b ∨
      gamma t 1 = c ∨ gamma t 1 = d := by
    by_contra hnone
    push Not at hnone
    have hxa : 0 < gamma t 0 - a := by
      exact sub_pos.mpr (lt_of_le_of_ne htRect.1 hnone.1.symm)
    have hbx : 0 < b - gamma t 0 := by
      exact sub_pos.mpr (lt_of_le_of_ne htRect.2.1 hnone.2.1)
    have hyc : 0 < gamma t 1 - c := by
      exact sub_pos.mpr (lt_of_le_of_ne htRect.2.2.1 hnone.2.2.1.symm)
    have hdy : 0 < d - gamma t 1 := by
      exact sub_pos.mpr (lt_of_le_of_ne htRect.2.2.2 hnone.2.2.2)
    have : 0 < rectangleMargin a b c d (gamma t) := by
      dsimp only [rectangleMargin]
      exact lt_min hxa (lt_min hbx (lt_min hyc hdy))
    change 0 < f t at this
    rw [htK] at this
    exact lt_irrefl _ this
  refine ⟨t, htK, ?_, ?_, htSide⟩
  · intro z hz
    rw [Path.range_subpath] at hz
    obtain ⟨u, huI, rfl⟩ := hz
    have hut : u ≤ t := by
      rw [Set.uIcc_of_le (show (0 : unitInterval) ≤ t from t.2.1)] at huI
      exact huI.2
    exact (rectangleMargin_nonneg_iff a b c d (gamma u)).1
      (hprefixNonneg u hut)
  · rw [Path.range_subpath]
    exact Set.image_subset_range _ _


theorem leftCrosscut_intersects_leftRightPath_of_left_between
    {a b c d : Real} (hab : a < b) (hcd : c < d)
    {lo hi start finish : Fin 2 → Real}
    (crosscut : Path lo hi) (escape : Path start finish)
    (hcrossRect : Set.range crosscut ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p})
    (hescapeRect : Set.range escape ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p})
    (hloX : lo 0 = a) (hhiX : hi 0 = a)
    (hstartX : start 0 = a) (hfinishX : finish 0 = b)
    (hloY : c ≤ lo 1) (hhiY : hi 1 ≤ d)
    (hescapeLeftBetween : ∀ p ∈ Set.range escape, p 0 = a →
      lo 1 < p 1 ∧ p 1 < hi 1) :
    (Set.range escape ∩ Set.range crosscut).Nonempty := by
  let bottom : Fin 2 → Real := ![a, c]
  let top : Fin 2 → Real := ![a, d]
  let lower : Path bottom lo := affinePath bottom lo
  let upper : Path hi top := affinePath hi top
  let vertical : Path bottom top := lower.trans (crosscut.trans upper)
  have hlowerRect : Set.range lower ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p} := by
    rintro p ⟨t, rfl⟩
    change a ≤ lower t 0 ∧ lower t 0 ≤ b ∧
      c ≤ lower t 1 ∧ lower t 1 ≤ d
    have ht0 := t.2.1
    have ht1 := t.2.2
    have hloRect : ContinuousRectangleCrossing.InRectangle a b c d lo := by
      simpa using hcrossRect (Set.mem_range_self (0 : unitInterval))
    dsimp only [lower, bottom]
    simp only [affinePath_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, hloX]
    constructor
    · ring_nf
      exact le_rfl
    constructor
    · linarith
    constructor <;> nlinarith [hloRect.2.2.2]
  have hupperRect : Set.range upper ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p} := by
    rintro p ⟨t, rfl⟩
    change a ≤ upper t 0 ∧ upper t 0 ≤ b ∧
      c ≤ upper t 1 ∧ upper t 1 ≤ d
    have ht0 := t.2.1
    have ht1 := t.2.2
    have hhiRect : ContinuousRectangleCrossing.InRectangle a b c d hi := by
      simpa using hcrossRect (Set.mem_range_self (1 : unitInterval))
    dsimp only [upper, top]
    simp only [affinePath_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, hhiX]
    constructor
    · ring_nf
      exact le_rfl
    constructor
    · linarith
    constructor <;> nlinarith [hhiRect.2.2.1]
  have hverticalRect : Set.range vertical ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p} := by
    rw [show Set.range vertical =
      Set.range lower ∪ (Set.range crosscut ∪ Set.range upper) by
        simp [vertical, Path.trans_range]]
    exact union_subset hlowerRect (union_subset hcrossRect hupperRect)
  obtain ⟨t, s, hts⟩ :=
    ContinuousRectangleCrossing.rectangle_paths_intersect
      hab hcd escape vertical hescapeRect hverticalRect
        hstartX hfinishX (by simp [bottom]) (by simp [top])
  have hsVertical : vertical s ∈ Set.range vertical := ⟨s, rfl⟩
  have hsCases : vertical s ∈ Set.range lower ∨
      vertical s ∈ Set.range crosscut ∨ vertical s ∈ Set.range upper := by
    simpa [vertical, Path.trans_range] using hsVertical
  rcases hsCases with hsLower | hsCrosscut | hsUpper
  · obtain ⟨u, hu⟩ := hsLower
    have hleft : escape t 0 = a := by
      rw [hts, ← hu]
      simp [lower, bottom, hloX]
      ring
    have hbetween := hescapeLeftBetween (escape t) ⟨t, rfl⟩ hleft
    have hyEq : escape t 1 = lower u 1 := by rw [hts, ← hu]
    have hu0 := u.2.1
    have hu1 := u.2.2
    dsimp only [lower, bottom] at hyEq
    change escape t 1 = (1 - (u : Real)) * c + (u : Real) * lo 1 at hyEq
    nlinarith
  · exact ⟨escape t, ⟨t, rfl⟩, by rwa [hts]⟩
  · obtain ⟨u, hu⟩ := hsUpper
    have hleft : escape t 0 = a := by
      rw [hts, ← hu]
      simp [upper, top, hhiX]
      ring
    have hbetween := hescapeLeftBetween (escape t) ⟨t, rfl⟩ hleft
    have hyEq : escape t 1 = upper u 1 := by rw [hts, ← hu]
    have hu0 := u.2.1
    have hu1 := u.2.2
    dsimp only [upper, top] at hyEq
    change escape t 1 = (1 - (u : Real)) * hi 1 + (u : Real) * d at hyEq
    nlinarith


theorem leftCrosscut_intersects_leftTopPath_of_left_between
    {a b c d : Real} (hab : a < b) (hcd : c < d)
    {lo hi start finish : Fin 2 → Real}
    (crosscut : Path lo hi) (escape : Path start finish)
    (hcrossRect : Set.range crosscut ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p})
    (hescapeRect : Set.range escape ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p})
    (hloX : lo 0 = a) (hhiX : hi 0 = a)
    (hstartX : start 0 = a) (hfinishY : finish 1 = d)
    (hfinishX : a < finish 0)
    (hloY : c ≤ lo 1) (hhiY : hi 1 ≤ d)
    (hescapeLeftBetween : ∀ p ∈ Set.range escape, p 0 = a →
      lo 1 < p 1 ∧ p 1 < hi 1)
    (hcrossBelowTop : ∀ t : unitInterval, crosscut t 1 < d) :
    (Set.range escape ∩ Set.range crosscut).Nonempty := by
  let topRight : Fin 2 → Real := ![b, d]
  let tail : Path finish topRight := affinePath finish topRight
  let extended : Path start topRight := escape.trans tail
  have htailRect : Set.range tail ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p} := by
    rintro p ⟨t, rfl⟩
    have ht0 := t.2.1
    have ht1 := t.2.2
    have hfinishRect : ContinuousRectangleCrossing.InRectangle a b c d finish := by
      simpa using hescapeRect (Set.mem_range_self (1 : unitInterval))
    change a ≤ tail t 0 ∧ tail t 0 ≤ b ∧
      c ≤ tail t 1 ∧ tail t 1 ≤ d
    dsimp only [tail, topRight]
    simp only [affinePath_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · nlinarith [hfinishRect.1]
    constructor
    · nlinarith [hfinishRect.2.1]
    constructor
    · rw [hfinishY]
      ring_nf
      exact hcd.le
    · rw [hfinishY]
      ring_nf
      exact le_rfl
  have hextendedRect : Set.range extended ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p} := by
    rw [show Set.range extended = Set.range escape ∪ Set.range tail by
      simp [extended, Path.trans_range]]
    exact union_subset hescapeRect htailRect
  have hextendedLeftBetween : ∀ p ∈ Set.range extended, p 0 = a →
      lo 1 < p 1 ∧ p 1 < hi 1 := by
    intro p hp hpLeft
    rw [show Set.range extended = Set.range escape ∪ Set.range tail by
      simp [extended, Path.trans_range]] at hp
    rcases hp with hpEscape | hpTail
    · exact hescapeLeftBetween p hpEscape hpLeft
    · obtain ⟨t, rfl⟩ := hpTail
      have ht0 := t.2.1
      have ht1 := t.2.2
      dsimp only [tail, topRight] at hpLeft
      simp only [affinePath_apply, Matrix.cons_val_zero] at hpLeft
      exfalso
      by_cases htOne : (t : Real) = 1
      · rw [htOne] at hpLeft
        norm_num at hpLeft
        linarith
      · have htLt : (t : Real) < 1 := lt_of_le_of_ne ht1 htOne
        have hfirst := mul_lt_mul_of_pos_left hfinishX (sub_pos.mpr htLt)
        have hsecond := mul_le_mul_of_nonneg_left hab.le ht0
        have ha : (1 - (t : Real)) * a + (t : Real) * a = a := by ring
        linarith
  have hinter := leftCrosscut_intersects_leftRightPath_of_left_between
    hab hcd crosscut extended hcrossRect hextendedRect hloX hhiX hstartX
      (by simp [topRight]) hloY hhiY hextendedLeftBetween
  obtain ⟨p, hpExtended, hpCrosscut⟩ := hinter
  rw [show Set.range extended = Set.range escape ∪ Set.range tail by
    simp [extended, Path.trans_range]] at hpExtended
  rcases hpExtended with hpEscape | hpTail
  · exact ⟨p, hpEscape, hpCrosscut⟩
  · obtain ⟨t, rfl⟩ := hpTail
    obtain ⟨s, hs⟩ := hpCrosscut
    have htailY : tail t 1 = d := by
      dsimp only [tail, topRight]
      change (1 - (t : Real)) * finish 1 + (t : Real) * d = d
      rw [hfinishY]
      ring
    have := hcrossBelowTop s
    have hsCoord := congrFun hs 1
    rw [htailY] at hsCoord
    linarith


theorem leftCrosscut_intersects_leftBottomPath_of_left_between
    {a b c d : Real} (hab : a < b) (hcd : c < d)
    {lo hi start finish : Fin 2 → Real}
    (crosscut : Path lo hi) (escape : Path start finish)
    (hcrossRect : Set.range crosscut ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p})
    (hescapeRect : Set.range escape ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p})
    (hloX : lo 0 = a) (hhiX : hi 0 = a)
    (hstartX : start 0 = a) (hfinishY : finish 1 = c)
    (hfinishX : a < finish 0)
    (hloY : c ≤ lo 1) (hhiY : hi 1 ≤ d)
    (hescapeLeftBetween : ∀ p ∈ Set.range escape, p 0 = a →
      lo 1 < p 1 ∧ p 1 < hi 1)
    (hcrossAboveBottom : ∀ t : unitInterval, c < crosscut t 1) :
    (Set.range escape ∩ Set.range crosscut).Nonempty := by
  let bottomRight : Fin 2 → Real := ![b, c]
  let tail : Path finish bottomRight := affinePath finish bottomRight
  let extended : Path start bottomRight := escape.trans tail
  have htailRect : Set.range tail ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p} := by
    rintro p ⟨t, rfl⟩
    have ht0 := t.2.1
    have ht1 := t.2.2
    have hfinishRect : ContinuousRectangleCrossing.InRectangle a b c d finish := by
      simpa using hescapeRect (Set.mem_range_self (1 : unitInterval))
    change a ≤ tail t 0 ∧ tail t 0 ≤ b ∧
      c ≤ tail t 1 ∧ tail t 1 ≤ d
    dsimp only [tail, bottomRight]
    simp only [affinePath_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · nlinarith [hfinishRect.1]
    constructor
    · nlinarith [hfinishRect.2.1]
    constructor
    · rw [hfinishY]
      ring_nf
      exact le_rfl
    · rw [hfinishY]
      ring_nf
      exact hcd.le
  have hextendedRect : Set.range extended ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p} := by
    rw [show Set.range extended = Set.range escape ∪ Set.range tail by
      simp [extended, Path.trans_range]]
    exact union_subset hescapeRect htailRect
  have hextendedLeftBetween : ∀ p ∈ Set.range extended, p 0 = a →
      lo 1 < p 1 ∧ p 1 < hi 1 := by
    intro p hp hpLeft
    rw [show Set.range extended = Set.range escape ∪ Set.range tail by
      simp [extended, Path.trans_range]] at hp
    rcases hp with hpEscape | hpTail
    · exact hescapeLeftBetween p hpEscape hpLeft
    · obtain ⟨t, rfl⟩ := hpTail
      have ht0 := t.2.1
      have ht1 := t.2.2
      dsimp only [tail, bottomRight] at hpLeft
      simp only [affinePath_apply, Matrix.cons_val_zero] at hpLeft
      exfalso
      by_cases htOne : (t : Real) = 1
      · rw [htOne] at hpLeft
        norm_num at hpLeft
        linarith
      · have htLt : (t : Real) < 1 := lt_of_le_of_ne ht1 htOne
        have hfirst := mul_lt_mul_of_pos_left hfinishX (sub_pos.mpr htLt)
        have hsecond := mul_le_mul_of_nonneg_left hab.le ht0
        have ha : (1 - (t : Real)) * a + (t : Real) * a = a := by ring
        linarith
  have hinter := leftCrosscut_intersects_leftRightPath_of_left_between
    hab hcd crosscut extended hcrossRect hextendedRect hloX hhiX hstartX
      (by simp [bottomRight]) hloY hhiY hextendedLeftBetween
  obtain ⟨p, hpExtended, hpCrosscut⟩ := hinter
  rw [show Set.range extended = Set.range escape ∪ Set.range tail by
    simp [extended, Path.trans_range]] at hpExtended
  rcases hpExtended with hpEscape | hpTail
  · exact ⟨p, hpEscape, hpCrosscut⟩
  · obtain ⟨t, rfl⟩ := hpTail
    obtain ⟨s, hs⟩ := hpCrosscut
    have htailY : tail t 1 = c := by
      dsimp only [tail, bottomRight]
      change (1 - (t : Real)) * finish 1 + (t : Real) * c = c
      rw [hfinishY]
      ring
    have := hcrossAboveBottom s
    have hsCoord := congrFun hs 1
    rw [htailY] at hsCoord
    linarith


theorem attachedCrosscut_intersection_reduces_to_core
    {lo hi x y start finish : Fin 2 → Real}
    (lower : Path lo x) (core : Path x y) (upper : Path y hi)
    (escape : Path start finish)
    (hinter : (Set.range escape ∩
      Set.range (lower.trans (core.trans upper))).Nonempty)
    (hlower : Disjoint (Set.range escape) (Set.range lower))
    (hupper : Disjoint (Set.range escape) (Set.range upper)) :
    (Set.range escape ∩ Set.range core).Nonempty := by
  obtain ⟨p, hpEscape, hpCrosscut⟩ := hinter
  have hpCases : p ∈ Set.range lower ∨
      p ∈ Set.range core ∨ p ∈ Set.range upper := by
    simpa only [Path.trans_range, Set.mem_union] using hpCrosscut
  rcases hpCases with hpLower | hpCore | hpUpper
  · exact (Set.disjoint_left.1 hlower hpEscape hpLower).elim
  · exact ⟨p, hpEscape, hpCore⟩
  · exact (Set.disjoint_left.1 hupper hpEscape hpUpper).elim


theorem doublyAttached_intersection_reduces_to_cores
    {plo px py phi estart eroot efinish : Fin 2 → Real}
    (plower : Path plo px) (pcore : Path px py) (pupper : Path py phi)
    (eprefix : Path estart eroot) (ecore : Path eroot efinish)
    (hinter : (Set.range (eprefix.trans ecore) ∩
      Set.range (plower.trans (pcore.trans pupper))).Nonempty)
    (hPrefixLower : Disjoint (Set.range eprefix) (Set.range plower))
    (hPrefixCore : Disjoint (Set.range eprefix) (Set.range pcore))
    (hPrefixUpper : Disjoint (Set.range eprefix) (Set.range pupper))
    (hCoreLower : Disjoint (Set.range ecore) (Set.range plower))
    (hCoreUpper : Disjoint (Set.range ecore) (Set.range pupper)) :
    (Set.range ecore ∩ Set.range pcore).Nonempty := by
  obtain ⟨z, hzEscape, hzPrimal⟩ := hinter
  have hzEscapeCases : z ∈ Set.range eprefix ∨ z ∈ Set.range ecore := by
    simpa only [Path.trans_range, Set.mem_union] using hzEscape
  have hzPrimalCases : z ∈ Set.range plower ∨
      z ∈ Set.range pcore ∨ z ∈ Set.range pupper := by
    simpa only [Path.trans_range, Set.mem_union] using hzPrimal
  rcases hzEscapeCases with hzPrefix | hzCore
  · rcases hzPrimalCases with hzLower | hzPCore | hzUpper
    · exact (Set.disjoint_left.1 hPrefixLower hzPrefix hzLower).elim
    · exact (Set.disjoint_left.1 hPrefixCore hzPrefix hzPCore).elim
    · exact (Set.disjoint_left.1 hPrefixUpper hzPrefix hzUpper).elim
  · rcases hzPrimalCases with hzLower | hzPCore | hzUpper
    · exact (Set.disjoint_left.1 hCoreLower hzCore hzLower).elim
    · exact ⟨z, hzCore, hzPCore⟩
    · exact (Set.disjoint_left.1 hCoreUpper hzCore hzUpper).elim


theorem leftCrosscut_intersects_leftRightPath
    {a b c d : Real} (hab : a < b) (hcd : c < d)
    {lo hi start finish : Fin 2 → Real}
    (crosscut : Path lo hi) (escape : Path start finish)
    (hcrossRect : Set.range crosscut ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p})
    (hescapeRect : Set.range escape ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p})
    (hloX : lo 0 = a) (hhiX : hi 0 = a)
    (hstartX : start 0 = a) (hfinishX : finish 0 = b)
    (hloY : c ≤ lo 1) (hhiY : hi 1 ≤ d)
    (horderLo : lo 1 < start 1) (horderHi : start 1 < hi 1)
    (hescapeLeft : ∀ p ∈ Set.range escape, p 0 = a → p = start) :
    (Set.range escape ∩ Set.range crosscut).Nonempty := by
  let bottom : Fin 2 → Real := ![a, c]
  let top : Fin 2 → Real := ![a, d]
  let lower : Path bottom lo := affinePath bottom lo
  let upper : Path hi top := affinePath hi top
  let vertical : Path bottom top := lower.trans (crosscut.trans upper)
  have hlowerRect : Set.range lower ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p} := by
    rintro p ⟨t, rfl⟩
    change a ≤ lower t 0 ∧ lower t 0 ≤ b ∧
      c ≤ lower t 1 ∧ lower t 1 ≤ d
    have ht0 := t.2.1
    have ht1 := t.2.2
    have hloRect : ContinuousRectangleCrossing.InRectangle a b c d lo := by
      simpa using hcrossRect (Set.mem_range_self (0 : unitInterval))
    dsimp only [lower, bottom]
    simp only [affinePath_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, hloX]
    constructor
    · ring_nf
      exact le_rfl
    constructor
    · linarith
    constructor <;> nlinarith [hloRect.2.2.2]
  have hupperRect : Set.range upper ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p} := by
    rintro p ⟨t, rfl⟩
    change a ≤ upper t 0 ∧ upper t 0 ≤ b ∧
      c ≤ upper t 1 ∧ upper t 1 ≤ d
    have ht0 := t.2.1
    have ht1 := t.2.2
    have hhiRect : ContinuousRectangleCrossing.InRectangle a b c d hi := by
      simpa using hcrossRect (Set.mem_range_self (1 : unitInterval))
    dsimp only [upper, top]
    simp only [affinePath_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, hhiX]
    constructor
    · ring_nf
      exact le_rfl
    constructor
    · linarith
    constructor <;> nlinarith [hhiRect.2.2.1]
  have hverticalRect : Set.range vertical ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p} := by
    rw [show Set.range vertical =
      Set.range lower ∪ (Set.range crosscut ∪ Set.range upper) by
        simp [vertical, Path.trans_range]]
    exact union_subset hlowerRect (union_subset hcrossRect hupperRect)
  obtain ⟨t, s, hts⟩ :=
    ContinuousRectangleCrossing.rectangle_paths_intersect
      hab hcd escape vertical hescapeRect hverticalRect
        hstartX hfinishX (by simp [bottom]) (by simp [top])
  have hsVertical : vertical s ∈ Set.range vertical := ⟨s, rfl⟩
  have hsCases : vertical s ∈ Set.range lower ∨
      vertical s ∈ Set.range crosscut ∨ vertical s ∈ Set.range upper := by
    simpa [vertical, Path.trans_range] using hsVertical
  rcases hsCases with hsLower | hsCrosscut | hsUpper
  · obtain ⟨u, hu⟩ := hsLower
    have hleft : escape t 0 = a := by
      rw [hts, ← hu]
      change lower u 0 = a
      simp [lower, bottom, hloX]
      ring
    have ht : escape t = start :=
      hescapeLeft (escape t) ⟨t, rfl⟩ hleft
    have hyEq : start 1 = lower u 1 := by
      rw [← ht, hts, ← hu]
    have hu0 := u.2.1
    have hu1 := u.2.2
    dsimp only [lower, bottom] at hyEq
    change start 1 = (1 - (u : Real)) * c + (u : Real) * lo 1 at hyEq
    nlinarith
  · exact ⟨escape t, ⟨t, rfl⟩, by rwa [hts]⟩
  · obtain ⟨u, hu⟩ := hsUpper
    have hleft : escape t 0 = a := by
      rw [hts, ← hu]
      change upper u 0 = a
      simp [upper, top, hhiX]
      ring
    have ht : escape t = start :=
      hescapeLeft (escape t) ⟨t, rfl⟩ hleft
    have hyEq : start 1 = upper u 1 := by
      rw [← ht, hts, ← hu]
    have hu0 := u.2.1
    have hu1 := u.2.2
    dsimp only [upper, top] at hyEq
    change start 1 = (1 - (u : Real)) * hi 1 + (u : Real) * d at hyEq
    nlinarith


theorem leftCrosscut_intersects_leftTopPath
    {a b c d : Real} (hab : a < b) (hcd : c < d)
    {lo hi start finish : Fin 2 → Real}
    (crosscut : Path lo hi) (escape : Path start finish)
    (hcrossRect : Set.range crosscut ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p})
    (hescapeRect : Set.range escape ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p})
    (hloX : lo 0 = a) (hhiX : hi 0 = a)
    (hstartX : start 0 = a) (hfinishY : finish 1 = d)
    (hfinishX : a < finish 0)
    (hloY : c ≤ lo 1) (hhiY : hi 1 ≤ d)
    (horderLo : lo 1 < start 1) (horderHi : start 1 < hi 1)
    (hescapeLeft : ∀ p ∈ Set.range escape, p 0 = a → p = start)
    (hcrossBelowTop : ∀ t : unitInterval, crosscut t 1 < d) :
    (Set.range escape ∩ Set.range crosscut).Nonempty := by
  let topRight : Fin 2 → Real := ![b, d]
  let tail : Path finish topRight := affinePath finish topRight
  let extended : Path start topRight := escape.trans tail
  have htailRect : Set.range tail ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p} := by
    rintro p ⟨t, rfl⟩
    have ht0 := t.2.1
    have ht1 := t.2.2
    have hfinishRect : ContinuousRectangleCrossing.InRectangle a b c d finish := by
      simpa using hescapeRect (Set.mem_range_self (1 : unitInterval))
    change a ≤ tail t 0 ∧ tail t 0 ≤ b ∧
      c ≤ tail t 1 ∧ tail t 1 ≤ d
    dsimp only [tail, topRight]
    simp only [affinePath_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · nlinarith [hfinishRect.1]
    constructor
    · nlinarith [hfinishRect.2.1]
    constructor
    · rw [hfinishY]
      ring_nf
      exact hcd.le
    · rw [hfinishY]
      ring_nf
      exact le_rfl
  have hextendedRect : Set.range extended ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p} := by
    rw [show Set.range extended = Set.range escape ∪ Set.range tail by
      simp [extended, Path.trans_range]]
    exact union_subset hescapeRect htailRect
  have hextendedLeft : ∀ p ∈ Set.range extended, p 0 = a → p = start := by
    intro p hp hpLeft
    rw [show Set.range extended = Set.range escape ∪ Set.range tail by
      simp [extended, Path.trans_range]] at hp
    rcases hp with hpEscape | hpTail
    · exact hescapeLeft p hpEscape hpLeft
    · obtain ⟨t, rfl⟩ := hpTail
      have ht0 := t.2.1
      have ht1 := t.2.2
      dsimp only [tail, topRight] at hpLeft
      simp only [affinePath_apply, Matrix.cons_val_zero] at hpLeft
      exfalso
      by_cases htOne : (t : Real) = 1
      · rw [htOne] at hpLeft
        norm_num at hpLeft
        linarith
      · have htLt : (t : Real) < 1 := lt_of_le_of_ne ht1 htOne
        have hfirst := mul_lt_mul_of_pos_left hfinishX (sub_pos.mpr htLt)
        have hsecond := mul_le_mul_of_nonneg_left hab.le ht0
        have ha : (1 - (t : Real)) * a + (t : Real) * a = a := by ring
        linarith
  have hinter := leftCrosscut_intersects_leftRightPath hab hcd
    crosscut extended hcrossRect hextendedRect hloX hhiX hstartX
      (by simp [topRight]) hloY hhiY horderLo horderHi hextendedLeft
  obtain ⟨p, hpExtended, hpCrosscut⟩ := hinter
  rw [show Set.range extended = Set.range escape ∪ Set.range tail by
    simp [extended, Path.trans_range]] at hpExtended
  rcases hpExtended with hpEscape | hpTail
  · exact ⟨p, hpEscape, hpCrosscut⟩
  · obtain ⟨t, rfl⟩ := hpTail
    obtain ⟨s, hs⟩ := hpCrosscut
    have htailY : tail t 1 = d := by
      dsimp only [tail, topRight]
      change (1 - (t : Real)) * finish 1 + (t : Real) * d = d
      rw [hfinishY]
      ring
    have := hcrossBelowTop s
    have hsCoord := congrFun hs 1
    rw [htailY] at hsCoord
    linarith


theorem leftCrosscut_intersects_leftBottomPath
    {a b c d : Real} (hab : a < b) (hcd : c < d)
    {lo hi start finish : Fin 2 → Real}
    (crosscut : Path lo hi) (escape : Path start finish)
    (hcrossRect : Set.range crosscut ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p})
    (hescapeRect : Set.range escape ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p})
    (hloX : lo 0 = a) (hhiX : hi 0 = a)
    (hstartX : start 0 = a) (hfinishY : finish 1 = c)
    (hfinishX : a < finish 0)
    (hloY : c ≤ lo 1) (hhiY : hi 1 ≤ d)
    (horderLo : lo 1 < start 1) (horderHi : start 1 < hi 1)
    (hescapeLeft : ∀ p ∈ Set.range escape, p 0 = a → p = start)
    (hcrossAboveBottom : ∀ t : unitInterval, c < crosscut t 1) :
    (Set.range escape ∩ Set.range crosscut).Nonempty := by
  let bottomRight : Fin 2 → Real := ![b, c]
  let tail : Path finish bottomRight := affinePath finish bottomRight
  let extended : Path start bottomRight := escape.trans tail
  have htailRect : Set.range tail ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p} := by
    rintro p ⟨t, rfl⟩
    have ht0 := t.2.1
    have ht1 := t.2.2
    have hfinishRect : ContinuousRectangleCrossing.InRectangle a b c d finish := by
      simpa using hescapeRect (Set.mem_range_self (1 : unitInterval))
    change a ≤ tail t 0 ∧ tail t 0 ≤ b ∧
      c ≤ tail t 1 ∧ tail t 1 ≤ d
    dsimp only [tail, bottomRight]
    simp only [affinePath_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · nlinarith [hfinishRect.1]
    constructor
    · nlinarith [hfinishRect.2.1]
    constructor
    · rw [hfinishY]
      ring_nf
      exact le_rfl
    · rw [hfinishY]
      ring_nf
      exact hcd.le
  have hextendedRect : Set.range extended ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p} := by
    rw [show Set.range extended = Set.range escape ∪ Set.range tail by
      simp [extended, Path.trans_range]]
    exact union_subset hescapeRect htailRect
  have hextendedLeft : ∀ p ∈ Set.range extended, p 0 = a → p = start := by
    intro p hp hpLeft
    rw [show Set.range extended = Set.range escape ∪ Set.range tail by
      simp [extended, Path.trans_range]] at hp
    rcases hp with hpEscape | hpTail
    · exact hescapeLeft p hpEscape hpLeft
    · obtain ⟨t, rfl⟩ := hpTail
      have ht0 := t.2.1
      have ht1 := t.2.2
      dsimp only [tail, bottomRight] at hpLeft
      simp only [affinePath_apply, Matrix.cons_val_zero] at hpLeft
      exfalso
      by_cases htOne : (t : Real) = 1
      · rw [htOne] at hpLeft
        norm_num at hpLeft
        linarith
      · have htLt : (t : Real) < 1 := lt_of_le_of_ne ht1 htOne
        have hfirst := mul_lt_mul_of_pos_left hfinishX (sub_pos.mpr htLt)
        have hsecond := mul_le_mul_of_nonneg_left hab.le ht0
        have ha : (1 - (t : Real)) * a + (t : Real) * a = a := by ring
        linarith
  have hinter := leftCrosscut_intersects_leftRightPath hab hcd
    crosscut extended hcrossRect hextendedRect hloX hhiX hstartX
      (by simp [bottomRight]) hloY hhiY horderLo horderHi hextendedLeft
  obtain ⟨p, hpExtended, hpCrosscut⟩ := hinter
  rw [show Set.range extended = Set.range escape ∪ Set.range tail by
    simp [extended, Path.trans_range]] at hpExtended
  rcases hpExtended with hpEscape | hpTail
  · exact ⟨p, hpEscape, hpCrosscut⟩
  · obtain ⟨t, rfl⟩ := hpTail
    obtain ⟨s, hs⟩ := hpCrosscut
    have htailY : tail t 1 = c := by
      dsimp only [tail, bottomRight]
      change (1 - (t : Real)) * finish 1 + (t : Real) * c = c
      rw [hfinishY]
      ring
    have := hcrossAboveBottom s
    have hsCoord := congrFun hs 1
    rw [htailY] at hsCoord
    linarith

end ContinuousHalfPlaneCrosscut


theorem PeriodicPlaneEmbedding.simpleWalkArc_coord_lower_of_support
    (E : PeriodicPlaneEmbedding P) {B r : Real}
    (hB0 : 0 ≤ B)
    (hB : ∀ {u v : V} (huv : P.graph.Adj u v) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc huv t - E.vertex u) i| ≤ B)
    (i : Fin 2) {x y : V} (p : P.graph.Walk x y)
    (hp : ∀ v ∈ p.support, r ≤ E.vertexCoord v i) :
    ∀ t : unitInterval,
      r - B ≤ E.coordinates (E.simpleWalkArc p t) i := by
  intro t
  have hq : E.simpleWalkArc p t ∈ Set.range (E.walkArc p) := by
    rw [← E.simpleWalkArc_range p]
    exact ⟨t, rfl⟩
  rcases E.mem_walkArc_range_cases p hq with hstart | hedge
  · change E.simpleWalkArc p t = E.vertex x at hstart
    rw [hstart]
    change r - B ≤ E.vertexCoord x i
    exact (sub_le_self r hB0).trans (hp x (by simp))
  · obtain ⟨u, v, huv, huvEdge, q, hqEdge⟩ := hedge
    have hu := hp u (p.fst_mem_support_of_mem_edges huvEdge)
    have hlo := E.vertex_sub_le_edgeArc_coord hB huv q i
    change E.edgeArc huv q = E.simpleWalkArc p t at hqEdge
    rw [← hqEdge]
    linarith


theorem PeriodicPlaneEmbedding.simpleWalkArc_coord_upper_of_support
    (E : PeriodicPlaneEmbedding P) {B r : Real}
    (hB0 : 0 ≤ B)
    (hB : ∀ {u v : V} (huv : P.graph.Adj u v) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc huv t - E.vertex u) i| ≤ B)
    (i : Fin 2) {x y : V} (p : P.graph.Walk x y)
    (hp : ∀ v ∈ p.support, E.vertexCoord v i ≤ r) :
    ∀ t : unitInterval,
      E.coordinates (E.simpleWalkArc p t) i ≤ r + B := by
  intro t
  have hq : E.simpleWalkArc p t ∈ Set.range (E.walkArc p) := by
    rw [← E.simpleWalkArc_range p]
    exact ⟨t, rfl⟩
  rcases E.mem_walkArc_range_cases p hq with hstart | hedge
  · change E.simpleWalkArc p t = E.vertex x at hstart
    rw [hstart]
    change E.vertexCoord x i ≤ r + B
    exact (hp x (by simp)).trans (le_add_of_nonneg_right hB0)
  · obtain ⟨u, v, huv, huvEdge, q, hqEdge⟩ := hedge
    have hu := hp u (p.fst_mem_support_of_mem_edges huvEdge)
    have hhi := E.edgeArc_coord_le_vertex_add hB huv q i
    change E.edgeArc huv q = E.simpleWalkArc p t at hqEdge
    rw [← hqEdge]
    linarith


theorem PeriodicPlaneEmbedding.exists_boundary_line_attachments
    (E : PeriodicPlaneEmbedding P) {B r c d : Real}
    (hB0 : 0 ≤ B)
    (hB : ∀ {v w : V} (hvw : P.graph.Adj v w) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hvw t - E.vertex v) i| ≤ B)
    {b u : V} (hb : b ∈ E.lowerBoundaryRayVertices r c)
    (hu : u ∈ E.upperBoundaryRayVertices r d) :
    ∃ lo hi : Fin 2 → Real,
      ∃ lower : Path lo (E.coordinates (E.vertex b)),
      ∃ upper : Path (E.coordinates (E.vertex u)) hi,
        lo 0 = r ∧ hi 0 = r ∧
        lo 1 ≤ c + B ∧ d - B ≤ hi 1 ∧
        (∀ z ∈ Set.range lower, z 1 ≤ c + B) ∧
        (∀ z ∈ Set.range upper, d - B ≤ z 1) ∧
        (∀ z ∈ Set.range lower, z 0 < r + 2 * B) ∧
        ∀ z ∈ Set.range upper, z 0 < r + 2 * B := by
  obtain ⟨_hbH, bOut, hbOut, hbOutX⟩ := hb.1
  obtain ⟨_huH, uOut, huOut, huOutX⟩ := hu.1
  let gammaB := (E.edgeArc hbOut).map E.coordinates.continuous
  let gammaU := (E.edgeArc huOut).map E.coordinates.continuous
  obtain ⟨tb, htb⟩ :=
    ContinuousHalfPlaneCrosscut.exists_parameter_coord_eq_of_ge
      gammaB 0 r hb.1.1 hbOutX.le
  obtain ⟨tu, htu⟩ :=
    ContinuousHalfPlaneCrosscut.exists_parameter_coord_eq_of_ge
      gammaU 0 r hu.1.1 huOutX.le
  let lo : Fin 2 → Real := gammaB tb
  let hi : Fin 2 → Real := gammaU tu
  let lower0 := (gammaB.subpath 0 tb).symm
  let upper0 := gammaU.subpath 0 tu
  let lower : Path lo (E.coordinates (E.vertex b)) :=
    lower0.cast rfl gammaB.source.symm
  let upper : Path (E.coordinates (E.vertex u)) hi :=
    upper0.cast gammaU.source.symm rfl
  have hloYDisp : |lo 1 - E.vertexCoord b 1| ≤ B := by
    have h := hB hbOut tb (1 : Fin 2)
    have heq : E.coordinates
        (E.edgeArc hbOut tb - E.vertex b) 1 =
        lo 1 - E.vertexCoord b 1 := by
      simp [lo, gammaB, PeriodicPlaneEmbedding.vertexCoord, map_sub]
    rwa [heq] at h
  have hhiYDisp : |hi 1 - E.vertexCoord u 1| ≤ B := by
    have h := hB huOut tu (1 : Fin 2)
    have heq : E.coordinates
        (E.edgeArc huOut tu - E.vertex u) 1 =
        hi 1 - E.vertexCoord u 1 := by
      simp [hi, gammaU, PeriodicPlaneEmbedding.vertexCoord, map_sub]
    rwa [heq] at h
  have hbX := E.rightHalfPlaneBoundary_coord_lt hB hb.1
  have huX := E.rightHalfPlaneBoundary_coord_lt hB hu.1
  have hlowerRange : Set.range lower ⊆ Set.range gammaB := by
    intro z hz
    have hz0 : z ∈ Set.range lower0 := by
      simpa [lower, Path.cast_coe] using hz
    dsimp only [lower0] at hz0
    rw [Path.symm_range, Path.range_subpath] at hz0
    obtain ⟨q, _hqI, hq⟩ := hz0
    exact ⟨q, hq⟩
  have hupperRange : Set.range upper ⊆ Set.range gammaU := by
    intro z hz
    have hz0 : z ∈ Set.range upper0 := by
      simpa [upper, Path.cast_coe] using hz
    dsimp only [upper0] at hz0
    rw [Path.range_subpath] at hz0
    obtain ⟨q, _hqI, hq⟩ := hz0
    exact ⟨q, hq⟩
  refine ⟨lo, hi, lower, upper, htb, htu, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hbY := hb.2
    change E.vertexCoord b 1 ≤ c at hbY
    linarith [abs_le.mp hloYDisp |>.2]
  · have huY := hu.2
    change d ≤ E.vertexCoord u 1 at huY
    linarith [abs_le.mp hhiYDisp |>.1]
  · intro z hz
    obtain ⟨q, hq⟩ := hlowerRange hz
    have hdisp := hB hbOut q (1 : Fin 2)
    have heq : gammaB q 1 - E.vertexCoord b 1 =
        E.coordinates (E.edgeArc hbOut q - E.vertex b) 1 := by
      simp [gammaB, PeriodicPlaneEmbedding.vertexCoord, map_sub]
    rw [← heq] at hdisp
    have hzEq := congrFun hq.symm 1
    have hbY := hb.2
    change E.vertexCoord b 1 ≤ c at hbY
    linarith [abs_le.mp hdisp |>.2]
  · intro z hz
    obtain ⟨q, hq⟩ := hupperRange hz
    have hdisp := hB huOut q (1 : Fin 2)
    have heq : gammaU q 1 - E.vertexCoord u 1 =
        E.coordinates (E.edgeArc huOut q - E.vertex u) 1 := by
      simp [gammaU, PeriodicPlaneEmbedding.vertexCoord, map_sub]
    rw [← heq] at hdisp
    have hzEq := congrFun hq.symm 1
    have huY := hu.2
    change d ≤ E.vertexCoord u 1 at huY
    linarith [abs_le.mp hdisp |>.1]
  · intro z hz
    obtain ⟨q, hq⟩ := hlowerRange hz
    have hdisp := hB hbOut q (0 : Fin 2)
    have heq : gammaB q 0 - E.vertexCoord b 0 =
        E.coordinates (E.edgeArc hbOut q - E.vertex b) 0 := by
      simp [gammaB, PeriodicPlaneEmbedding.vertexCoord, map_sub]
    rw [← heq] at hdisp
    have hzEq := congrFun hq.symm 0
    linarith [abs_le.mp hdisp |>.2]
  · intro z hz
    obtain ⟨q, hq⟩ := hupperRange hz
    have hdisp := hB huOut q (0 : Fin 2)
    have heq : gammaU q 0 - E.vertexCoord u 0 =
        E.coordinates (E.edgeArc huOut q - E.vertex u) 0 := by
      simp [gammaU, PeriodicPlaneEmbedding.vertexCoord, map_sub]
    rw [← heq] at hdisp
    have hzEq := congrFun hq.symm 0
    linarith [abs_le.mp hdisp |>.2]

omit [Countable V] in


theorem PeriodicGraph.exists_open_boundary_walk_of_walk_to_compl
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) (A : Set V)
    {x y : V} (p : (P.openSubgraph omega).Walk x y)
    (hx : x ∈ A) (hy : y ∉ A) :
    ∃ b ∈ A, ∃ z : V, (P.openSubgraph omega).Adj b z ∧ z ∉ A ∧
      ∃ q : (P.openSubgraph omega).Walk x b,
        (∀ v ∈ q.support, v ∈ A) ∧
        (∀ v ∈ q.support, v ∈ p.support) ∧ z ∈ p.support := by
  induction p with
  | nil => exact (hy hx).elim
  | @cons x z y hxz p ih =>
      by_cases hz : z ∈ A
      · obtain ⟨b, hb, w, hbw, hw, q, hqA, hqp, hwSupport⟩ := ih hz hy
        refine ⟨b, hb, w, hbw, hw, q.cons hxz, ?_, ?_, ?_⟩
        · intro v hv
          rw [SimpleGraph.Walk.support_cons] at hv
          rcases List.mem_cons.mp hv with rfl | hv
          · exact hx
          · exact hqA v hv
        · intro v hv
          rw [SimpleGraph.Walk.support_cons] at hv ⊢
          rcases List.mem_cons.mp hv with rfl | hv
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem x (hqp v hv)
        · exact List.mem_cons_of_mem x hwSupport
      · refine ⟨x, hx, z, hxz, hz, .nil, ?_, ?_, ?_⟩
        · simpa using hx
        · intro v hv
          rw [SimpleGraph.Walk.support_nil] at hv
          rw [SimpleGraph.Walk.support_cons]
          have hvx : v = x := by simpa using hv
          exact List.mem_cons.2 (Or.inl hvx)
        · simp


end StatMech.FK.PeriodicPlanar
