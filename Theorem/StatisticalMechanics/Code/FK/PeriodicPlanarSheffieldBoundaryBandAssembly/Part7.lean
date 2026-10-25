/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryBandPadding.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldExclusion
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDeepTemplateGridAssembly
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryBandAssembly.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}


theorem exists_alternating_dominating_sequences (f g : Nat → Nat) :
    ∃ x y : Nat → Nat,
      Tendsto x atTop atTop ∧ Tendsto y atTop atTop ∧
      (∀ n, f (x n) ≤ y n) ∧
      (∀ n, g (y n) ≤ x (n + 1)) := by
  let state : Nat → Nat × Nat := fun n =>
    Nat.rec (0, f 0) (fun k previous =>
      let x := max (k + 1) (g previous.2)
      (x, max (k + 1) (f x))) n
  let x : Nat → Nat := fun n => (state n).1
  let y : Nat → Nat := fun n => (state n).2
  have hxLower (n : Nat) : n ≤ x n := by
    cases n with
    | zero => simp [x, state]
    | succ n => simp [x, state]
  have hyLower (n : Nat) : n ≤ y n := by
    cases n with
    | zero => simp [y, state]
    | succ n => simp [y, state]
  have hxy (n : Nat) : f (x n) ≤ y n := by
    cases n with
    | zero => simp [x, y, state]
    | succ n => simp [x, y, state]
  have hyx (n : Nat) : g (y n) ≤ x (n + 1) := by
    simp [x, y, state]
  refine ⟨x, y, ?_, ?_, hxy, hyx⟩
  · rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    exact hn.trans (hxLower n)
  · rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    exact hn.trans (hyLower n)

omit [Countable V] in


theorem normalBand_left_source_aligned
    (baseLeft gridBase : Site 2) (i j : Nat) :
    baseLeft + horizontalShift i +
        (gridBase - baseLeft + verticalShift j) =
      gridBase + horizontalShift i + verticalShift j := by
  abel

omit [Countable V] in

theorem normalBand_right_source_aligned
    (baseRight gridBase : Site 2) (width i j : Nat) :
    baseRight + horizontalShift (-(i : Int)) +
        (gridBase - baseRight + horizontalShift width + verticalShift j) =
      gridBase + horizontalShift ((width : Int) - i) + verticalShift j := by
  funext k
  fin_cases k <;> simp [horizontalShift, verticalShift] <;> omega

omit [Countable V] in

theorem normalBand_bottom_source_aligned
    (baseBottom gridBase : Site 2) (i j : Nat) :
    baseBottom + verticalShift j +
        (gridBase - baseBottom + horizontalShift i) =
      gridBase + horizontalShift i + verticalShift j := by
  abel

omit [Countable V] in

theorem normalBand_top_source_aligned
    (baseTop gridBase : Site 2) (height i j : Nat) :
    baseTop + verticalShift (-(j : Int)) +
        (gridBase - baseTop + verticalShift height + horizontalShift i) =
      gridBase + horizontalShift i + verticalShift ((height : Int) - j) := by
  funext k
  fin_cases k <;> simp [horizontalShift, verticalShift] <;> omega


theorem PeriodicPlaneEmbedding.setHitsInfinite_subset_mixedRectSideConnection_union
    (E : PeriodicPlaneEmbedding P)
    (a0 b0 c0 d0 a1 b1 c1 d1 : Real) (S : Set V)
    (ha : a1 ≤ a0) (hb : b0 ≤ b1) (hc : c0 ≤ c1) (hd : d1 ≤ d0)
    (hS : S ⊆ E.rectVertices a0 b0 c1 d1) :
    P.setHitsInfinite S ⊆
      E.rectSideConnectionEvent a1 b1 c1 d1 S
          (E.rectBottomBoundaryVertices a1 b1 c1 d1) ∪
        (E.rectSideConnectionEvent a1 b1 c1 d1 S
            (E.rectTopBoundaryVertices a1 b1 c1 d1) ∪
          (E.rectSideConnectionEvent a0 b0 c0 d0 S
              (E.rectLeftBoundaryVertices a0 b0 c0 d0) ∪
            E.rectSideConnectionEvent a0 b0 c0 d0 S
              (E.rectRightBoundaryVertices a0 b0 c0 d0))) := by
  intro omega homega
  have hcover := E.setHitsInfinite_subset_rectSideConnection_union
    a0 b0 c1 d1 S hS homega
  rcases hcover with hbottom | htop | hleft | hright
  · exact Or.inl (E.rectBottomConnectionEvent_mono_otherBounds S
      ha hb (le_refl d1) hbottom)
  · exact Or.inr (Or.inl (E.rectTopConnectionEvent_mono_otherBounds S
      ha hb (le_refl c1) htop))
  · exact Or.inr (Or.inr (Or.inl
      (E.rectLeftConnectionEvent_mono_otherBounds S
        (le_refl b0) hc hd hleft)))
  · exact Or.inr (Or.inr (Or.inr
      (E.rectRightConnectionEvent_mono_otherBounds S
        (le_refl a0) hc hd hright)))


theorem PeriodicPlaneEmbedding.preference_mixed_max_add_epsilon_ge_fourthRoot
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu)
    (a0 b0 c0 d0 a1 b1 c1 d1 : Real) (S : Set V)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (ha : a1 ≤ a0) (hb : b0 ≤ b1) (hc : c0 ≤ c1) (hd : d1 ≤ d0)
    (hS : S ⊆ E.rectVertices a0 b0 c1 d1)
    (hBottomTop : mu.real (E.rectSideConnectionEvent a1 b1 c1 d1 S
        (E.rectTopBoundaryVertices a1 b1 c1 d1)) ≤
      mu.real (E.rectSideConnectionEvent a1 b1 c1 d1 S
        (E.rectBottomBoundaryVertices a1 b1 c1 d1)) + epsilon)
    (hLeftRight : mu.real (E.rectSideConnectionEvent a0 b0 c0 d0 S
        (E.rectRightBoundaryVertices a0 b0 c0 d0)) ≤
      mu.real (E.rectSideConnectionEvent a0 b0 c0 d0 S
        (E.rectLeftBoundaryVertices a0 b0 c0 d0)) + epsilon) :
    1 - Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite S))) ≤
      max
        (mu.real (E.rectSideConnectionEvent a1 b1 c1 d1 S
          (E.rectBottomBoundaryVertices a1 b1 c1 d1)))
        (mu.real (E.rectSideConnectionEvent a0 b0 c0 d0 S
          (E.rectLeftBoundaryVertices a0 b0 c0 d0))) + epsilon := by
  let B := E.rectSideConnectionEvent a1 b1 c1 d1 S
    (E.rectBottomBoundaryVertices a1 b1 c1 d1)
  let T := E.rectSideConnectionEvent a1 b1 c1 d1 S
    (E.rectTopBoundaryVertices a1 b1 c1 d1)
  let L := E.rectSideConnectionEvent a0 b0 c0 d0 S
    (E.rectLeftBoundaryVertices a0 b0 c0 d0)
  let R := E.rectSideConnectionEvent a0 b0 c0 d0 S
    (E.rectRightBoundaryVertices a0 b0 c0 d0)
  have hfour := four_event_sqrt_trick mu hFKG
    (E.rectSideConnectionEvent_isIncreasing a1 b1 c1 d1 S
      (E.rectBottomBoundaryVertices a1 b1 c1 d1))
    (E.rectSideConnectionEvent_isIncreasing a1 b1 c1 d1 S
      (E.rectTopBoundaryVertices a1 b1 c1 d1))
    (E.rectSideConnectionEvent_isIncreasing a0 b0 c0 d0 S
      (E.rectLeftBoundaryVertices a0 b0 c0 d0))
    (E.rectSideConnectionEvent_isIncreasing a0 b0 c0 d0 S
      (E.rectRightBoundaryVertices a0 b0 c0 d0))
    (E.rectSideConnectionEvent_measurableSet a1 b1 c1 d1 S
      (E.rectBottomBoundaryVertices a1 b1 c1 d1))
    (E.rectSideConnectionEvent_measurableSet a1 b1 c1 d1 S
      (E.rectTopBoundaryVertices a1 b1 c1 d1))
    (E.rectSideConnectionEvent_measurableSet a0 b0 c0 d0 S
      (E.rectLeftBoundaryVertices a0 b0 c0 d0))
    (E.rectSideConnectionEvent_measurableSet a0 b0 c0 d0 S
      (E.rectRightBoundaryVertices a0 b0 c0 d0))
  have hmass : mu.real (P.setHitsInfinite S) ≤
      mu.real (B ∪ (T ∪ (L ∪ R))) := measureReal_mono
    (E.setHitsInfinite_subset_mixedRectSideConnection_union
      a0 b0 c0 d0 a1 b1 c1 d1 S ha hb hc hd hS)
  have hsqrt : Real.sqrt (Real.sqrt
      (1 - mu.real (B ∪ (T ∪ (L ∪ R))))) ≤
        Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite S))) := by
    gcongr
  have hB : mu.real B ≤ max (mu.real B) (mu.real L) + epsilon :=
    (le_max_left _ _).trans (le_add_of_nonneg_right hepsilon)
  have hL : mu.real L ≤ max (mu.real B) (mu.real L) + epsilon :=
    (le_max_right _ _).trans (le_add_of_nonneg_right hepsilon)
  have hT : mu.real T ≤ max (mu.real B) (mu.real L) + epsilon := by
    dsimp only [B, T, L, R] at hBottomTop ⊢
    linarith [le_max_left (mu.real B) (mu.real L)]
  have hR : mu.real R ≤ max (mu.real B) (mu.real L) + epsilon := by
    dsimp only [B, T, L, R] at hLeftRight ⊢
    linarith [le_max_right (mu.real B) (mu.real L)]
  have hmax : max (max (mu.real B) (mu.real T))
      (max (mu.real L) (mu.real R)) ≤
        max (mu.real B) (mu.real L) + epsilon :=
    max_le (max_le hB hT) (max_le hL hR)
  dsimp only [B, T, L, R] at hfour hsqrt hmax ⊢
  linarith


theorem PeriodicPlaneEmbedding.exists_mixed_approxPreferredSide_crossing_branch
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu)
    (a0 b0 c0 d0 a1 b1 c1 d1 : Real)
    {width height : Nat} (hwidth : 0 < width) (hheight : 0 < height)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (source : PreferenceGridVertex width height → Finset V)
    (bottom top left right : PreferenceGridVertex width height → Real)
    (ha : a1 ≤ a0) (hb : b0 ≤ b1) (hc : c0 ≤ c1) (hd : d1 ≤ d0)
    (hsource : ∀ x, (source x : Set V) ⊆
      E.rectVertices a0 b0 c1 d1)
    (hbottomScore : ∀ x, bottom x = mu.real
      (E.rectSideConnectionEvent a1 b1 c1 d1 (source x : Set V)
        (E.rectBottomBoundaryVertices a1 b1 c1 d1)))
    (htopScore : ∀ x, top x = mu.real
      (E.rectSideConnectionEvent a1 b1 c1 d1 (source x : Set V)
        (E.rectTopBoundaryVertices a1 b1 c1 d1)))
    (hleftScore : ∀ x, left x = mu.real
      (E.rectSideConnectionEvent a0 b0 c0 d0 (source x : Set V)
        (E.rectLeftBoundaryVertices a0 b0 c0 d0)))
    (hrightScore : ∀ x, right x = mu.real
      (E.rectSideConnectionEvent a0 b0 c0 d0 (source x : Set V)
        (E.rectRightBoundaryVertices a0 b0 c0 d0)))
    (hbottom : ∀ i : Fin (width + 1),
      top (i, 0) ≤ bottom (i, 0) + epsilon)
    (htop : ∀ i : Fin (width + 1),
      bottom (i, Fin.last height) ≤ top (i, Fin.last height) + epsilon)
    (hleft : ∀ j : Fin (height + 1),
      right (0, j) ≤ left (0, j) + epsilon)
    (hright : ∀ j : Fin (height + 1),
      left (Fin.last width, j) ≤ right (Fin.last width, j) + epsilon) :
    ∃ x xVertical xHorizontal : PreferenceGridVertex width height,
      KingAdj (preferenceGridSite x) (preferenceGridSite xVertical) ∧
      KingAdj (preferenceGridSite x) (preferenceGridSite xHorizontal) ∧
      ((1 - Real.sqrt (Real.sqrt
            (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤
          bottom x + epsilon ∧
        bottom x *
            (mu.real (P.setHitsInfinite (source xVertical : Set V)) * bottom x -
              mu.real (E.rectanglePairMergeErrorUnion a1 b1 c1 d1
                (source x) (source xVertical)) - epsilon) -
            mu.real (E.rectanglePairMergeErrorUnion a1 b1 c1 d1
              (source x) (source xVertical)) ≤
          mu.real (E.verticalCrossingEvent a1 b1 c1 d1)) ∨
       (1 - Real.sqrt (Real.sqrt
            (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤
          left x + epsilon ∧
        left x *
            (mu.real (P.setHitsInfinite (source xHorizontal : Set V)) * left x -
              mu.real (E.rectanglePairMergeErrorUnion a0 b0 c0 d0
                (source x) (source xHorizontal)) - epsilon) -
            mu.real (E.rectanglePairMergeErrorUnion a0 b0 c0 d0
              (source x) (source xHorizontal)) ≤
          mu.real (E.horizontalCrossingEvent a0 b0 c0 d0))) := by
  obtain ⟨x, xVertical, xHorizontal, hxBottom, hxLeft,
      hxVertical, hxVerticalOpposite, hxHorizontal, hxHorizontalOpposite⟩ :=
    exists_common_weak_approximate_preference_grid_witness
      hwidth hheight epsilon hepsilon bottom top left right
      hbottom htop hleft hright
  have hpref := E.preference_mixed_max_add_epsilon_ge_fourthRoot mu hFKG
    a0 b0 c0 d0 a1 b1 c1 d1 (source x : Set V) epsilon hepsilon
    ha hb hc hd (hsource x)
    (by simpa [hbottomScore x, htopScore x] using hxBottom)
    (by simpa [hleftScore x, hrightScore x] using hxLeft)
  have hpref' :
      1 - Real.sqrt (Real.sqrt
          (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤
        max (bottom x) (left x) + epsilon := by
    simpa [hbottomScore x, hleftScore x] using hpref
  refine ⟨x, xVertical, xHorizontal, hxVertical, hxHorizontal, ?_⟩
  by_cases hLB : left x ≤ bottom x
  · left
    have hroot : 1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤
        bottom x + epsilon := by simpa [max_eq_left hLB] using hpref'
    have htransfer := E.verticalCrossing_ge_approxPreferredSide_transfer
      mu hFKG a1 b1 c1 d1 (source x) (source xVertical) epsilon
      (by simpa [hbottomScore xVertical, htopScore xVertical] using
        hxVerticalOpposite)
    rw [← hbottomScore x] at htransfer
    exact ⟨hroot, htransfer⟩
  · right
    have hBL : bottom x ≤ left x := le_of_not_ge hLB
    have hroot : 1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤
        left x + epsilon := by simpa [max_eq_right hBL] using hpref'
    have htransfer := E.horizontalCrossing_ge_approxPreferredSide_transfer
      mu hFKG a0 b0 c0 d0 (source x) (source xHorizontal) epsilon
      (by simpa [hleftScore xHorizontal, hrightScore xHorizontal] using
        hxHorizontalOpposite)
    rw [← hleftScore x] at htransfer
    exact ⟨hroot, htransfer⟩

set_option linter.unusedVariables false in


theorem PeriodicPlaneEmbedding.exists_uniformTemplate_mixedGridPreference_crossing_max_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (template : Nat → Finset V)
    (htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1)) :
    ∃ radius : Nat → Nat, ∀
      (width height : Nat → Nat)
      (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n)
      (base : Nat → Site 2)
      (a0 b0 c0 d0 a1 b1 c1 d1 epsilon : Nat → Real)
      (bottom top left right : (n : Nat) →
        PreferenceGridVertex (width n) (height n) → Real),
      Tendsto epsilon atTop (nhds 0) → (∀ n, 0 ≤ epsilon n) →
      (∀ n, a1 n ≤ a0 n) → (∀ n, b0 n ≤ b1 n) →
      (∀ n, c0 n ≤ c1 n) → (∀ n, d1 n ≤ d0 n) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        ((template n).image
        (P.shift (base n + preferenceGridSite v)) : Set V) ⊆
          E.rectVertices (a0 n) (b0 n) (c1 n) (d1 n)) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (base n + preferenceGridSite v) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
          E.rectVertices (a0 n) (b0 n) (c0 n) (d0 n)) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (base n + preferenceGridSite v) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
          E.rectVertices (a1 n) (b1 n) (c1 n) (d1 n)) →
      (∀ n v, bottom n v = mu.real
        (E.rectSideConnectionEvent (a1 n) (b1 n) (c1 n) (d1 n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectBottomBoundaryVertices (a1 n) (b1 n) (c1 n) (d1 n)))) →
      (∀ n v, top n v = mu.real
        (E.rectSideConnectionEvent (a1 n) (b1 n) (c1 n) (d1 n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectTopBoundaryVertices (a1 n) (b1 n) (c1 n) (d1 n)))) →
      (∀ n v, left n v = mu.real
        (E.rectSideConnectionEvent (a0 n) (b0 n) (c0 n) (d0 n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectLeftBoundaryVertices (a0 n) (b0 n) (c0 n) (d0 n)))) →
      (∀ n v, right n v = mu.real
        (E.rectSideConnectionEvent (a0 n) (b0 n) (c0 n) (d0 n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectRightBoundaryVertices (a0 n) (b0 n) (c0 n) (d0 n)))) →
      (∀ n i, top n (i, 0) ≤ bottom n (i, 0) + epsilon n) →
      (∀ n i, bottom n (i, Fin.last (height n)) ≤
        top n (i, Fin.last (height n)) + epsilon n) →
      (∀ n j, right n (0, j) ≤ left n (0, j) + epsilon n) →
      (∀ n j, left n (Fin.last (width n), j) ≤
        right n (Fin.last (width n), j) + epsilon n) →
      Tendsto (fun n => max
        (mu.real (E.horizontalCrossingEvent
          (a0 n) (b0 n) (c0 n) (d0 n)))
        (mu.real (E.verticalCrossingEvent
          (a1 n) (b1 n) (c1 n) (d1 n)))) atTop (nhds 1) := by
  let neighbor : Nat → (Fin 3 × Fin 3) → Finset V := fun n ij =>
    (template n).image (P.shift (preferenceKingOffset ij))
  obtain ⟨radius, _hradius, hmerge⟩ :=
    E.exists_uniform_translatedTemplate_mergeError_tendsto_zero
      mu hTI hunique template neighbor
  refine ⟨radius, ?_⟩
  intro width height hwidth hheight base a0 b0 c0 d0 a1 b1 c1 d1 epsilon
    bottom top left right hepsilon hepsilon0 ha hb hc hd hsource
    hconnector0 hconnector1 hbottomScore htopScore hleftScore hrightScore
    hbottom htop hleft hright
  have hwitness (n : Nat) :=
    E.exists_mixed_approxPreferredSide_crossing_branch mu hFKG
      (a0 n) (b0 n) (c0 n) (d0 n) (a1 n) (b1 n) (c1 n) (d1 n)
      (hwidth n) (hheight n) (epsilon n) (hepsilon0 n)
      (fun v => (template n).image
        (P.shift (base n + preferenceGridSite v)))
      (bottom n) (top n) (left n) (right n)
      (ha n) (hb n) (hc n) (hd n) (hsource n)
      (hbottomScore n) (htopScore n) (hleftScore n) (hrightScore n)
      (hbottom n) (htop n) (hleft n) (hright n)
  choose x xVertical xHorizontal hxVadj hxHadj hbranch using hwitness
  choose ijV hijV using fun n =>
    exists_preferenceKingOffset_of_kingAdj (hxVadj n)
  choose ijH hijH using fun n =>
    exists_preferenceKingOffset_of_kingAdj (hxHadj n)
  let source : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Finset V := fun n v =>
    (template n).image (P.shift (base n + preferenceGridSite v))
  let z : Nat → Site 2 := fun n => base n + preferenceGridSite (x n)
  have hzV (n : Nat) : z n + preferenceKingOffset (ijV n) =
      base n + preferenceGridSite (xVertical n) := by
    dsimp only [z]
    rw [hijV n]
    simp only [add_assoc]
  have hzH (n : Nat) : z n + preferenceKingOffset (ijH n) =
      base n + preferenceGridSite (xHorizontal n) := by
    dsimp only [z]
    rw [hijH n]
    simp only [add_assoc]
  have hneighbor (n : Nat) (ij : Fin 3 × Fin 3) :
      (neighbor n ij).image (P.shift (z n)) =
        (template n).image
          (P.shift (z n + preferenceKingOffset ij)) := by
    simp only [neighbor, Finset.image_image]
    apply Finset.image_congr
    intro u hu
    simpa [add_comm] using
      (P.shift_add (preferenceKingOffset ij) (z n) u).symm
  have hMv0 := hmerge z ijV a1 b1 c1 d1
    (fun n => hconnector1 n (x n))
  have hMh0 := hmerge z ijH a0 b0 c0 d0
    (fun n => hconnector0 n (x n))
  let Mv : Nat → Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a1 n) (b1 n) (c1 n) (d1 n)
      (source n (x n)) (source n (xVertical n)))
  let Mh : Nat → Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a0 n) (b0 n) (c0 n) (d0 n)
      (source n (x n)) (source n (xHorizontal n)))
  have hMv : Tendsto Mv atTop (nhds 0) := by
    simpa only [Mv, source, z, hneighbor, hzV] using hMv0
  have hMh : Tendsto Mh atTop (nhds 0) := by
    simpa only [Mh, source, z, hneighbor, hzH] using hMh0
  let verticalBranch : Nat → Prop := fun n =>
    1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.setHitsInfinite (source n (x n) : Set V)))) ≤
          bottom n (x n) + epsilon n ∧
      bottom n (x n) *
          (mu.real (P.setHitsInfinite
              (source n (xVertical n) : Set V)) * bottom n (x n) -
            Mv n - epsilon n) - Mv n ≤
        mu.real (E.verticalCrossingEvent
          (a1 n) (b1 n) (c1 n) (d1 n))
  let A : Nat → Real := fun n =>
    if verticalBranch n then bottom n (x n) else left n (x n)
  let Hv : Nat → Real := fun n =>
    mu.real (P.setHitsInfinite (source n (xVertical n) : Set V))
  let Hh : Nat → Real := fun n =>
    mu.real (P.setHitsInfinite (source n (xHorizontal n) : Set V))
  let Cv : Nat → Real := fun n => mu.real
    (E.verticalCrossingEvent (a1 n) (b1 n) (c1 n) (d1 n))
  let Ch : Nat → Real := fun n => mu.real
    (E.horizontalCrossingEvent (a0 n) (b0 n) (c0 n) (d0 n))
  let root : Nat → Real := fun n =>
    1 - Real.sqrt (Real.sqrt
      (1 - mu.real (P.setHitsInfinite (source n (x n) : Set V))))
  have htranslatedHit (y : (n : Nat) →
      PreferenceGridVertex (width n) (height n)) : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (source n (y n) : Set V)))
      atTop (nhds 1) := by
    apply htemplateHit.congr'
    filter_upwards with n
    have hset : ((source n (y n) : Finset V) : Set V) =
        P.shift (base n + preferenceGridSite (y n)) ''
          (template n : Set V) := by
      ext v
      simp [source]
    rw [hset, P.setHitsInfinite_translate_measureReal_eq mu hTI]
  have hroot : Tendsto root atTop (nhds 1) := by
    have hhit := htranslatedHit x
    have hmiss : Tendsto (fun n =>
        1 - mu.real (P.setHitsInfinite (source n (x n) : Set V)))
        atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub hhit
    simpa [root] using tendsto_const_nhds.sub hmiss.sqrt.sqrt
  have hHv : Tendsto Hv atTop (nhds 1) := by
    simpa [Hv] using htranslatedHit xVertical
  have hHh : Tendsto Hh atTop (nhds 1) := by
    simpa [Hh] using htranslatedHit xHorizontal
  have hrootA (n : Nat) : root n ≤ A n + epsilon n := by
    by_cases hv : verticalBranch n
    · simpa [A, root, hv] using hv.1
    · simpa [A, root, source, hv] using ((hbranch n).resolve_left hv).1
  have hAupper (n : Nat) : A n ≤ 1 := by
    by_cases hv : verticalBranch n
    · simp only [A, if_pos hv]
      rw [hbottomScore n (x n)]
      exact measureReal_le_one
    · simp only [A, if_neg hv]
      rw [hleftScore n (x n)]
      exact measureReal_le_one
  have hcrossingBranch (n : Nat) :
      A n * (Hv n * A n - Mv n - epsilon n) - Mv n ≤ Cv n ∨
      A n * (Hh n * A n - Mh n - epsilon n) - Mh n ≤ Ch n := by
    by_cases hv : verticalBranch n
    · left
      simpa [A, Hv, Cv, hv] using hv.2
    · right
      have h := (hbranch n).resolve_left hv
      simpa [A, Hh, Ch, Mh, source, hv] using h.2
  simpa [Cv, Ch, max_comm] using
    crossing_max_tendsto_one_of_approxPreferredSide_root_branches
      root A Hv Hh Mv Mh epsilon Cv Ch hroot hrootA hAupper
      hHv hHh hMv hMh hepsilon hcrossingBranch
      (fun _ => measureReal_le_one) (fun _ => measureReal_le_one)

set_option linter.unusedVariables false in


theorem PeriodicPlaneEmbedding.exists_uniformTemplate_mixedBoundaryScores_crossing_max_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (template : Nat → Finset V)
    (htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1)) :
    ∃ radius : Nat → Nat, ∀
      (width height : Nat → Nat)
      (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n)
      (base : Nat → Site 2)
      (a0 b0 c0 d0 a1 b1 c1 d1 p : Nat → Real),
      Tendsto p atTop (nhds 1) → (∀ n, p n ≤ 1) →
      (∀ n, a1 n ≤ a0 n) → (∀ n, b0 n ≤ b1 n) →
      (∀ n, c0 n ≤ c1 n) → (∀ n, d1 n ≤ d0 n) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V) ⊆
            E.rectVertices (a0 n) (b0 n) (c1 n) (d1 n)) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (base n + preferenceGridSite v) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (a0 n) (b0 n) (c0 n) (d0 n)) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (base n + preferenceGridSite v) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (a1 n) (b1 n) (c1 n) (d1 n)) →
      (∀ n (i : Fin (width n + 1)), p n ≤ mu.real
        (E.rectSideConnectionEvent (a1 n) (b1 n) (c1 n) (d1 n)
          ((template n).image (P.shift (base n + preferenceGridSite
            (i, (0 : Fin (height n + 1))))) : Set V)
          (E.rectBottomBoundaryVertices (a1 n) (b1 n) (c1 n) (d1 n)))) →
      (∀ n (i : Fin (width n + 1)), p n ≤ mu.real
        (E.rectSideConnectionEvent (a1 n) (b1 n) (c1 n) (d1 n)
          ((template n).image (P.shift (base n + preferenceGridSite
            (i, Fin.last (height n)))) : Set V)
          (E.rectTopBoundaryVertices (a1 n) (b1 n) (c1 n) (d1 n)))) →
      (∀ n (j : Fin (height n + 1)), p n ≤ mu.real
        (E.rectSideConnectionEvent (a0 n) (b0 n) (c0 n) (d0 n)
          ((template n).image (P.shift (base n + preferenceGridSite
            ((0 : Fin (width n + 1)), j))) : Set V)
          (E.rectLeftBoundaryVertices (a0 n) (b0 n) (c0 n) (d0 n)))) →
      (∀ n (j : Fin (height n + 1)), p n ≤ mu.real
        (E.rectSideConnectionEvent (a0 n) (b0 n) (c0 n) (d0 n)
          ((template n).image (P.shift (base n + preferenceGridSite
            (Fin.last (width n), j))) : Set V)
          (E.rectRightBoundaryVertices (a0 n) (b0 n) (c0 n) (d0 n)))) →
      Tendsto (fun n => max
        (mu.real (E.horizontalCrossingEvent
          (a0 n) (b0 n) (c0 n) (d0 n)))
        (mu.real (E.verticalCrossingEvent
          (a1 n) (b1 n) (c1 n) (d1 n)))) atTop (nhds 1) := by
  obtain ⟨radius, hcross⟩ :=
    E.exists_uniformTemplate_mixedGridPreference_crossing_max_tendsto_one
      mu hFKG hTI hunique template htemplateHit
  refine ⟨radius, ?_⟩
  intro width height hwidth hheight base a0 b0 c0 d0 a1 b1 c1 d1 p
    hplim hp ha hb hc hd hsource hconnector0 hconnector1
    hbottom htop hleft hright
  let epsilon : Nat → Real := fun n => 1 - p n
  let bottom : (n : Nat) → PreferenceGridVertex (width n) (height n) → Real :=
    fun n v => mu.real (E.rectSideConnectionEvent
      (a1 n) (b1 n) (c1 n) (d1 n)
      ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectBottomBoundaryVertices (a1 n) (b1 n) (c1 n) (d1 n)))
  let top : (n : Nat) → PreferenceGridVertex (width n) (height n) → Real :=
    fun n v => mu.real (E.rectSideConnectionEvent
      (a1 n) (b1 n) (c1 n) (d1 n)
      ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectTopBoundaryVertices (a1 n) (b1 n) (c1 n) (d1 n)))
  let left : (n : Nat) → PreferenceGridVertex (width n) (height n) → Real :=
    fun n v => mu.real (E.rectSideConnectionEvent
      (a0 n) (b0 n) (c0 n) (d0 n)
      ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectLeftBoundaryVertices (a0 n) (b0 n) (c0 n) (d0 n)))
  let right : (n : Nat) → PreferenceGridVertex (width n) (height n) → Real :=
    fun n v => mu.real (E.rectSideConnectionEvent
      (a0 n) (b0 n) (c0 n) (d0 n)
      ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectRightBoundaryVertices (a0 n) (b0 n) (c0 n) (d0 n)))
  apply hcross width height hwidth hheight base
    a0 b0 c0 d0 a1 b1 c1 d1 epsilon bottom top left right
  · simpa [epsilon] using
      (tendsto_const_nhds (x := (1 : Real))).sub hplim
  · exact fun n => sub_nonneg.mpr (hp n)
  · exact ha
  · exact hb
  · exact hc
  · exact hd
  · exact hsource
  · exact hconnector0
  · exact hconnector1
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n i
    have hTop : top n (i, 0) ≤ 1 := measureReal_le_one
    have hBottom := hbottom n i
    dsimp only [top, bottom, epsilon]
    linarith
  · intro n i
    have hBottom : bottom n (i, Fin.last (height n)) ≤ 1 := measureReal_le_one
    have hTop := htop n i
    dsimp only [top, bottom, epsilon]
    linarith
  · intro n j
    have hRight : right n (0, j) ≤ 1 := measureReal_le_one
    have hLeft := hleft n j
    dsimp only [left, right, epsilon]
    linarith
  · intro n j
    have hLeft : left n (Fin.last (width n), j) ≤ 1 := measureReal_le_one
    have hRight := hright n j
    dsimp only [left, right, epsilon]
    linarith

set_option linter.unusedVariables false in


theorem PeriodicPlaneEmbedding.exists_uniformRadius_boundaryBandScores_crossing_max_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
    ∃ radius : Nat → Nat, ∀
      (width height margin : Nat → Nat)
      (base : Nat → Site 2) (a b c d p : Nat → Real),
      (∀ n, 2 * margin n < width n) →
      (∀ n, 2 * margin n < height n) →
      (∀ n, p n ≤ 1) → Tendsto p atTop (nhds 1) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        ((P.orbitBox n).image
          (P.shift (base n + preferenceGridSite v)) : Set V) ⊆
            E.rectVertices (a n) (b n) (c n) (d n)) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        margin n ≤ v.1.val → v.1.val + margin n < width n →
        margin n ≤ v.2.val → v.2.val + margin n < height n →
        (P.shift (base n + preferenceGridSite v) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (a n) (b n) (c n) (d n)) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        v.2.val ≤ margin n → p n ≤ mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((P.orbitBox n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        height n ≤ v.2.val + margin n → p n ≤ mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((P.orbitBox n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        v.1.val ≤ margin n → p n ≤ mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((P.orbitBox n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        width n ≤ v.1.val + margin n → p n ≤ mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((P.orbitBox n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) →
      Tendsto (fun n => max
        (mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n)))
        (mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n))))
        atTop (nhds 1) := by
  let template : Nat → Finset V := fun n => P.orbitBox n
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [← hunique]
    exact measure_mono fun _ h => h.1
  have htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V)))
      atTop (nhds 1) := by
    simpa only [template, PeriodicGraph.setHitsInfinite,
      PeriodicGraph.orbitBoxHitsInfinite] using
      P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  obtain ⟨radius, hcross⟩ :=
    E.exists_uniformTemplate_deepGridPreference_crossing_max_tendsto_one
      mu hFKG hTI hunique template htemplateHit
  refine ⟨radius, ?_⟩
  intro width height margin base a b c d p hwidthSep hheightSep hp hplim
    hsource hconnector hbottom htop hleft hright
  let epsilon : Nat → Real := fun n => 1 - p n
  let bottom : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Real := fun n v =>
    mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      ((P.orbitBox n).image
        (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))
  let top : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Real := fun n v =>
    mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      ((P.orbitBox n).image
        (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))
  let left : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Real := fun n v =>
    mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      ((P.orbitBox n).image
        (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))
  let right : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Real := fun n v =>
    mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      ((P.orbitBox n).image
        (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))
  let vertical : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Bool := fun n v =>
    boundaryBandPreferenceColor (margin n) (height n) v.2.val
      (epsilon n) (bottom n v) (top n v)
  let horizontal : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Bool := fun n v =>
    boundaryBandPreferenceColor (margin n) (width n) v.1.val
      (epsilon n) (left n v) (right n v)
  have hepsilon : Tendsto epsilon atTop (nhds 0) := by
    simpa [epsilon] using
      (tendsto_const_nhds (x := (1 : Real))).sub hplim
  apply hcross width height margin
    (fun n => (Nat.zero_le (2 * margin n)).trans_lt (hwidthSep n))
    base vertical horizontal
    a b c d epsilon bottom top left right hepsilon
  · exact fun n => sub_nonneg.mpr (hp n)
  · simpa only [template] using hsource
  · exact hconnector
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n v hv
    exact boundaryBandPreferenceColor_eq_true_of_lower hv
  · intro n v hv
    exact boundaryBandPreferenceColor_eq_false_of_upper
      (hheightSep n) hv
  · intro n v hv
    exact boundaryBandPreferenceColor_eq_true_of_lower hv
  · intro n v hv
    exact boundaryBandPreferenceColor_eq_false_of_upper
      (hwidthSep n) hv
  · intro n v hv
    apply boundaryBandPreferenceColor_true_imp
      (sub_nonneg.mpr (hp n)) (hheightSep n) measureReal_le_one
      (fun h => hbottom n v h) (le_refl _) hv
  · intro n v hv
    apply boundaryBandPreferenceColor_false_imp
      (sub_nonneg.mpr (hp n)) (hheightSep n) measureReal_le_one
      (fun h => htop n v h) (le_refl _) hv
  · intro n v hv
    apply boundaryBandPreferenceColor_true_imp
      (sub_nonneg.mpr (hp n)) (hwidthSep n) measureReal_le_one
      (fun h => hleft n v h) (le_refl _) hv
  · intro n v hv
    apply boundaryBandPreferenceColor_false_imp
      (sub_nonneg.mpr (hp n)) (hwidthSep n) measureReal_le_one
      (fun h => hright n v h) (le_refl _) hv

end StatMech.FK.PeriodicPlanar
