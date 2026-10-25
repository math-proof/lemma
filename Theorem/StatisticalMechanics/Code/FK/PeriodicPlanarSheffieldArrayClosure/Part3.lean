/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldMacroArrayAssembly.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldArrayClosure
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

omit [Countable V] in
theorem PeriodicGraph.bottom_subset_fourBoundaryComponentTemplate
    (P : PeriodicGraph V) (bottom top left right : Finset V) :
    bottom ⊆ P.fourBoundaryComponentTemplate bottom top left right := by
  intro x hx
  simp [PeriodicGraph.fourBoundaryComponentTemplate, hx]

omit [Countable V] in
theorem PeriodicGraph.top_subset_fourBoundaryComponentTemplate
    (P : PeriodicGraph V) (bottom top left right : Finset V) :
    top ⊆ P.fourBoundaryComponentTemplate bottom top left right := by
  intro x hx
  simp [PeriodicGraph.fourBoundaryComponentTemplate, hx]

omit [Countable V] in
theorem PeriodicGraph.left_subset_fourBoundaryComponentTemplate
    (P : PeriodicGraph V) (bottom top left right : Finset V) :
    left ⊆ P.fourBoundaryComponentTemplate bottom top left right := by
  intro x hx
  simp [PeriodicGraph.fourBoundaryComponentTemplate, hx]

omit [Countable V] in
theorem PeriodicGraph.right_subset_fourBoundaryComponentTemplate
    (P : PeriodicGraph V) (bottom top left right : Finset V) :
    right ⊆ P.fourBoundaryComponentTemplate bottom top left right := by
  intro x hx
  simp [PeriodicGraph.fourBoundaryComponentTemplate, hx]


theorem PeriodicPlaneEmbedding.exists_sharedBoundaryComponentTemplate
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (p a b c d : Real)
    (bottom top left right : Finset V)
    (aBottom bBottom dBottom aTop bTop cTop : Real)
    (bLeft cLeft dLeft aRight cRight dRight : Real)
    (hBottomSource : (bottom : Set V) ⊆
      E.rectVertices aBottom bBottom c dBottom)
    (hTopSource : (top : Set V) ⊆
      E.rectVertices aTop bTop cTop d)
    (hLeftSource : (left : Set V) ⊆
      E.rectVertices a bLeft cLeft dLeft)
    (hRightSource : (right : Set V) ⊆
      E.rectVertices aRight b cRight dRight)
    (hBottomScore : p < mu.real (E.rectSideConnectionEvent
      aBottom bBottom c dBottom (bottom : Set V)
      (E.rectBottomBoundaryVertices aBottom bBottom c dBottom)))
    (hTopScore : p < mu.real (E.rectSideConnectionEvent
      aTop bTop cTop d (top : Set V)
      (E.rectTopBoundaryVertices aTop bTop cTop d)))
    (hLeftScore : p < mu.real (E.rectSideConnectionEvent
      a bLeft cLeft dLeft (left : Set V)
      (E.rectLeftBoundaryVertices a bLeft cLeft dLeft)))
    (hRightScore : p < mu.real (E.rectSideConnectionEvent
      aRight b cRight dRight (right : Set V)
      (E.rectRightBoundaryVertices aRight b cRight dRight)))
    (hBottomA : a ≤ aBottom) (hBottomB : bBottom ≤ b)
    (hBottomD : dBottom ≤ d)
    (hTopA : a ≤ aTop) (hTopB : bTop ≤ b) (hTopC : c ≤ cTop)
    (hLeftB : bLeft ≤ b) (hLeftC : c ≤ cLeft) (hLeftD : dLeft ≤ d)
    (hRightA : a ≤ aRight) (hRightC : c ≤ cRight)
    (hRightD : dRight ≤ d) :
    let template := P.fourBoundaryComponentTemplate bottom top left right
    (template : Set V) ⊆ E.rectVertices a b c d ∧
      p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V)
        (E.rectBottomBoundaryVertices a b c d)) ∧
      p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V)
        (E.rectTopBoundaryVertices a b c d)) ∧
      p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V)
        (E.rectLeftBoundaryVertices a b c d)) ∧
      p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V)
        (E.rectRightBoundaryVertices a b c d)) := by
  dsimp only
  let template := P.fourBoundaryComponentTemplate bottom top left right
  have hBottomCommon : (bottom : Set V) ⊆ E.rectVertices a b c d :=
    hBottomSource.trans (E.rectVertices_mono hBottomA hBottomB le_rfl hBottomD)
  have hTopCommon : (top : Set V) ⊆ E.rectVertices a b c d :=
    hTopSource.trans (E.rectVertices_mono hTopA hTopB hTopC le_rfl)
  have hLeftCommon : (left : Set V) ⊆ E.rectVertices a b c d :=
    hLeftSource.trans (E.rectVertices_mono le_rfl hLeftB hLeftC hLeftD)
  have hRightCommon : (right : Set V) ⊆ E.rectVertices a b c d :=
    hRightSource.trans (E.rectVertices_mono hRightA le_rfl hRightC hRightD)
  have htemplate : (template : Set V) ⊆ E.rectVertices a b c d := by
    intro x hx
    simp only [template, PeriodicGraph.fourBoundaryComponentTemplate,
      Finset.mem_coe, Finset.mem_union] at hx
    rcases hx with (hx | hx) | (hx | hx)
    · exact hBottomCommon hx
    · exact hTopCommon hx
    · exact hLeftCommon hx
    · exact hRightCommon hx
  have hBottom := E.rectBottomConnection_component_le_template_of_enlarge
    (c := c) mu bottom template (P.bottom_subset_fourBoundaryComponentTemplate
      bottom top left right) hBottomA hBottomB hBottomD
  have hTop := E.rectTopConnection_component_le_template_of_enlarge
    (d := d) mu top template (P.top_subset_fourBoundaryComponentTemplate
      bottom top left right) hTopA hTopB hTopC
  have hLeft := E.rectLeftConnection_component_le_template_of_enlarge
    (a := a) mu left template (P.left_subset_fourBoundaryComponentTemplate
      bottom top left right) hLeftB hLeftC hLeftD
  have hRight := E.rectRightConnection_component_le_template_of_enlarge
    (b := b) mu right template (P.right_subset_fourBoundaryComponentTemplate
      bottom top left right) hRightA hRightC hRightD
  exact ⟨htemplate, hBottomScore.trans_le hBottom,
    hTopScore.trans_le hTop, hLeftScore.trans_le hLeft,
    hRightScore.trans_le hRight⟩


theorem PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_endpointSources
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (verticalMargin horizontalMargin : Nat)
    (a0 b0 c0 d0 a1 b1 c1 d1 : Int)
    (hbottomWidth : 2 * (family.radiusBottom verticalMargin : Int) ≤ b0 - a0)
    (htopWidth : 2 * (family.radiusTop verticalMargin : Int) ≤ b0 - a0)
    (hbottomHeight : (family.radiusBottom verticalMargin : Int) ≤ d0 - c0)
    (htopHeight : (family.radiusTop verticalMargin : Int) ≤ d0 - c0)
    (hleftWidth : (family.radiusLeft horizontalMargin : Int) ≤ b1 - a1)
    (hrightWidth : (family.radiusRight horizontalMargin : Int) ≤ b1 - a1)
    (hleftHeight : 2 * (family.radiusLeft horizontalMargin : Int) ≤ d1 - c1)
    (hrightHeight : 2 * (family.radiusRight horizontalMargin : Int) ≤ d1 - c1) :
    ∃ bottomSource topSource leftSource rightSource : Finset V,
      (bottomSource : Set V) ⊆ E.rectVertices a0 b0 c0 d0 ∧
      p < mu.real (E.rectSideConnectionEvent a0 b0 c0 d0
        (bottomSource : Set V) (E.rectBottomBoundaryVertices a0 b0 c0 d0)) ∧
      (topSource : Set V) ⊆ E.rectVertices a0 b0 c0 d0 ∧
      p < mu.real (E.rectSideConnectionEvent a0 b0 c0 d0
        (topSource : Set V) (E.rectTopBoundaryVertices a0 b0 c0 d0)) ∧
      (leftSource : Set V) ⊆ E.rectVertices a1 b1 c1 d1 ∧
      p < mu.real (E.rectSideConnectionEvent a1 b1 c1 d1
        (leftSource : Set V) (E.rectLeftBoundaryVertices a1 b1 c1 d1)) ∧
      (rightSource : Set V) ⊆ E.rectVertices a1 b1 c1 d1 ∧
      p < mu.real (E.rectSideConnectionEvent a1 b1 c1 d1
        (rightSource : Set V) (E.rectRightBoundaryVertices a1 b1 c1 d1)) := by
  let verticalSeed := family.seed E verticalMargin
  let horizontalSeed := family.seed E horizontalMargin
  let zBottom : Site 2 :=
    horizontalShift (a0 + family.radiusBottom verticalMargin) + verticalShift c0
  let zTop : Site 2 :=
    horizontalShift (a0 + family.radiusTop verticalMargin) + verticalShift d0
  let zLeft : Site 2 :=
    horizontalShift a1 + verticalShift (c1 + family.radiusLeft horizontalMargin)
  let zRight : Site 2 :=
    horizontalShift b1 + verticalShift (c1 + family.radiusRight horizontalMargin)
  let bottomSource : Finset V :=
    (S.image (P.shift (family.baseBottom + verticalShift 0))).image
      (P.shift zBottom)
  let topSource : Finset V :=
    (S.image (P.shift (family.baseTop + verticalShift 0))).image
      (P.shift zTop)
  let leftSource : Finset V :=
    (S.image (P.shift (family.baseLeft + horizontalShift 0))).image
      (P.shift zLeft)
  let rightSource : Finset V :=
    (S.image (P.shift (family.baseRight + horizontalShift 0))).image
      (P.shift zRight)
  have hbottom := verticalSeed.bottom_translate_to_rect E mu hTI
    (0 : Fin (verticalMargin + 1)) zBottom (a0 : Real) (b0 : Real) (d0 : Real)
    (by
      dsimp only [verticalSeed,
        PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zBottom]
      simp)
    (by
      dsimp only [verticalSeed,
        PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zBottom]
      simp only [Pi.add_apply, horizontalShift_zero_apply,
        verticalShift_zero_apply, Int.cast_add, Int.cast_natCast,
        Int.cast_zero, add_zero]
      change (family.radiusBottom verticalMargin : Real) +
          ((a0 : Real) + family.radiusBottom verticalMargin) ≤ (b0 : Real)
      have hw : a0 + (family.radiusBottom verticalMargin : Int) +
          family.radiusBottom verticalMargin ≤ b0 := by omega
      have hwR : (a0 : Real) + family.radiusBottom verticalMargin +
          family.radiusBottom verticalMargin ≤ b0 := by exact_mod_cast hw
      linarith)
    (by
      dsimp only [verticalSeed,
        PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zBottom]
      simp only [horizontalShift_one_apply, Int.cast_zero, add_zero,
        Int.cast_natCast, Pi.add_apply, verticalShift_one_apply,
        Int.cast_add, zero_add]
      have hh : (c0 : Real) + family.radiusBottom verticalMargin ≤ d0 := by
        exact_mod_cast (by omega : c0 +
          (family.radiusBottom verticalMargin : Int) ≤ d0)
      simpa [add_comm] using hh)
  have htop := verticalSeed.top_translate_to_rect E mu hTI
    (0 : Fin (verticalMargin + 1)) zTop (a0 : Real) (b0 : Real) (c0 : Real)
    (by
      dsimp only [verticalSeed,
        PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zTop]
      simp)
    (by
      dsimp only [verticalSeed,
        PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zTop]
      simp only [Pi.add_apply, horizontalShift_zero_apply,
        verticalShift_zero_apply, Int.cast_add, Int.cast_natCast,
        Int.cast_zero, add_zero]
      have hw : a0 + (family.radiusTop verticalMargin : Int) +
          family.radiusTop verticalMargin ≤ b0 := by omega
      have hwR : (a0 : Real) + family.radiusTop verticalMargin +
          family.radiusTop verticalMargin ≤ b0 := by exact_mod_cast hw
      linarith)
    (by
      dsimp only [verticalSeed,
        PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zTop]
      simp only [Pi.add_apply, horizontalShift_one_apply,
        verticalShift_one_apply, Int.cast_add, Int.cast_natCast,
        Int.cast_zero, zero_add]
      have hh : (c0 : Real) ≤ d0 - family.radiusTop verticalMargin := by
        exact_mod_cast (by omega : c0 ≤ d0 -
          (family.radiusTop verticalMargin : Int))
      linarith)
  have hleft := horizontalSeed.left_translate_to_rect E mu hTI
    (0 : Fin (horizontalMargin + 1)) zLeft (b1 : Real) (c1 : Real) (d1 : Real)
    (by
      dsimp only [horizontalSeed,
        PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zLeft]
      simp only [Pi.add_apply, horizontalShift_zero_apply,
        verticalShift_zero_apply, Int.cast_add, Int.cast_zero, add_zero]
      have hw : (a1 : Real) + family.radiusLeft horizontalMargin ≤ b1 := by
        exact_mod_cast (by omega : a1 +
          (family.radiusLeft horizontalMargin : Int) ≤ b1)
      linarith)
    (by
      dsimp only [horizontalSeed,
        PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zLeft]
      simp)
    (by
      dsimp only [horizontalSeed,
        PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zLeft]
      simp only [Pi.add_apply, horizontalShift_one_apply,
        verticalShift_one_apply, Int.cast_add, Int.cast_natCast,
        Int.cast_zero, zero_add]
      have hh : c1 + (family.radiusLeft horizontalMargin : Int) +
          family.radiusLeft horizontalMargin ≤ d1 := by omega
      have hhR : (c1 : Real) + family.radiusLeft horizontalMargin +
          family.radiusLeft horizontalMargin ≤ d1 := by exact_mod_cast hh
      linarith)
  have hright := horizontalSeed.right_translate_to_rect E mu hTI
    (0 : Fin (horizontalMargin + 1)) zRight (a1 : Real) (c1 : Real) (d1 : Real)
    (by
      dsimp only [horizontalSeed,
        PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zRight]
      simp only [Pi.add_apply, horizontalShift_zero_apply,
        verticalShift_zero_apply, Int.cast_add, Int.cast_zero, add_zero]
      have hw : (a1 : Real) ≤ b1 - family.radiusRight horizontalMargin := by
        exact_mod_cast (by omega : a1 ≤ b1 -
          (family.radiusRight horizontalMargin : Int))
      linarith)
    (by
      dsimp only [horizontalSeed,
        PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zRight]
      simp)
    (by
      dsimp only [horizontalSeed,
        PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zRight]
      simp only [Pi.add_apply, horizontalShift_one_apply,
        verticalShift_one_apply, Int.cast_add, Int.cast_natCast,
        Int.cast_zero, zero_add]
      have hh : c1 + (family.radiusRight horizontalMargin : Int) +
          family.radiusRight horizontalMargin ≤ d1 := by omega
      have hhR : (c1 : Real) + family.radiusRight horizontalMargin +
          family.radiusRight horizontalMargin ≤ d1 := by exact_mod_cast hh
      linarith)
  refine ⟨bottomSource, topSource, leftSource, rightSource, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [bottomSource, topSource, leftSource, rightSource,
      Finset.coe_image] at ⊢
  · simpa [verticalSeed,
      PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zBottom] using hbottom.1
  · simpa [verticalSeed,
      PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zBottom] using hbottom.2
  · simpa [verticalSeed,
      PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zTop] using htop.1
  · simpa [verticalSeed,
      PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zTop] using htop.2
  · simpa [horizontalSeed,
      PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zLeft] using hleft.1
  · simpa [horizontalSeed,
      PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zLeft] using hleft.2
  · simpa [horizontalSeed,
      PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zRight] using hright.1
  · simpa [horizontalSeed,
      PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zRight] using hright.2


theorem PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_sharedEndpointTemplate
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (verticalMargin horizontalMargin : Nat) (a b c d : Int)
    (hbottomWidth : 2 * (family.radiusBottom verticalMargin : Int) ≤ b - a)
    (htopWidth : 2 * (family.radiusTop verticalMargin : Int) ≤ b - a)
    (hbottomHeight : (family.radiusBottom verticalMargin : Int) ≤ d - c)
    (htopHeight : (family.radiusTop verticalMargin : Int) ≤ d - c)
    (hleftWidth : (family.radiusLeft horizontalMargin : Int) ≤ b - a)
    (hrightWidth : (family.radiusRight horizontalMargin : Int) ≤ b - a)
    (hleftHeight : 2 * (family.radiusLeft horizontalMargin : Int) ≤ d - c)
    (hrightHeight : 2 * (family.radiusRight horizontalMargin : Int) ≤ d - c) :
    ∃ bottom top left right : Finset V,
      let template := P.fourBoundaryComponentTemplate bottom top left right
      (template : Set V) ⊆ E.rectVertices a b c d ∧
      p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V)
        (E.rectBottomBoundaryVertices a b c d)) ∧
      p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V)
        (E.rectTopBoundaryVertices a b c d)) ∧
      p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V)
        (E.rectLeftBoundaryVertices a b c d)) ∧
      p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V)
        (E.rectRightBoundaryVertices a b c d)) := by
  obtain ⟨bottom, top, left, right, hbottomSource, hbottomScore,
      htopSource, htopScore, hleftSource, hleftScore,
      hrightSource, hrightScore⟩ :=
    family.exists_endpointSources E mu hTI verticalMargin horizontalMargin
      a b c d a b c d hbottomWidth htopWidth hbottomHeight htopHeight
      hleftWidth hrightWidth hleftHeight hrightHeight
  refine ⟨bottom, top, left, right, ?_⟩
  exact E.exists_sharedBoundaryComponentTemplate mu p a b c d
    bottom top left right a b d a b c b c d a c d
    hbottomSource htopSource hleftSource hrightSource
    hbottomScore htopScore hleftScore hrightScore
    le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
    le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl


theorem PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_sharedEndpointComponents
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (verticalMargin horizontalMargin : Nat) (a b c d : Int)
    (hbottomWidth : 2 * (family.radiusBottom verticalMargin : Int) ≤ b - a)
    (htopWidth : 2 * (family.radiusTop verticalMargin : Int) ≤ b - a)
    (hbottomHeight : (family.radiusBottom verticalMargin : Int) ≤ d - c)
    (htopHeight : (family.radiusTop verticalMargin : Int) ≤ d - c)
    (hleftWidth : (family.radiusLeft horizontalMargin : Int) ≤ b - a)
    (hrightWidth : (family.radiusRight horizontalMargin : Int) ≤ b - a)
    (hleftHeight : 2 * (family.radiusLeft horizontalMargin : Int) ≤ d - c)
    (hrightHeight : 2 * (family.radiusRight horizontalMargin : Int) ≤ d - c) :
    ∃ bottom top left right : Finset V,
      (bottom : Set V) ⊆ E.rectVertices a b c d ∧
      p < mu.real (E.rectSideConnectionEvent a b c d (bottom : Set V)
        (E.rectBottomBoundaryVertices a b c d)) ∧
      (top : Set V) ⊆ E.rectVertices a b c d ∧
      p < mu.real (E.rectSideConnectionEvent a b c d (top : Set V)
        (E.rectTopBoundaryVertices a b c d)) ∧
      (left : Set V) ⊆ E.rectVertices a b c d ∧
      p < mu.real (E.rectSideConnectionEvent a b c d (left : Set V)
        (E.rectLeftBoundaryVertices a b c d)) ∧
      (right : Set V) ⊆ E.rectVertices a b c d ∧
      p < mu.real (E.rectSideConnectionEvent a b c d (right : Set V)
        (E.rectRightBoundaryVertices a b c d)) ∧
      let template := P.fourBoundaryComponentTemplate bottom top left right
      (template : Set V) ⊆ E.rectVertices a b c d ∧
      p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V)
        (E.rectBottomBoundaryVertices a b c d)) ∧
      p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V)
        (E.rectTopBoundaryVertices a b c d)) ∧
      p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V)
        (E.rectLeftBoundaryVertices a b c d)) ∧
      p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V)
        (E.rectRightBoundaryVertices a b c d)) := by
  obtain ⟨bottom, top, left, right, hbottomSource, hbottomScore,
      htopSource, htopScore, hleftSource, hleftScore,
      hrightSource, hrightScore⟩ :=
    family.exists_endpointSources E mu hTI verticalMargin horizontalMargin
      a b c d a b c d hbottomWidth htopWidth hbottomHeight htopHeight
      hleftWidth hrightWidth hleftHeight hrightHeight
  have hshared := E.exists_sharedBoundaryComponentTemplate mu p a b c d
    bottom top left right a b d a b c b c d a c d
    hbottomSource htopSource hleftSource hrightSource
    hbottomScore htopScore hleftScore hrightScore
    le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
    le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
  exact ⟨bottom, top, left, right,
    hbottomSource, hbottomScore, htopSource, htopScore,
    hleftSource, hleftScore, hrightSource, hrightScore, hshared⟩


theorem PeriodicPlaneEmbedding.NormalBoundaryBandFamily.commonBoundaryScores
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (horizontalMargin verticalMargin width height : Nat)
    (hleftBottom : (family.radiusLeft horizontalMargin : Int) +
      family.baseLeft 1 ≤ family.baseBottom 1 + verticalMargin)
    (hrightBottom : (family.radiusRight horizontalMargin : Int) +
      family.baseRight 1 ≤ family.baseBottom 1 + verticalMargin)
    (hleftTop : (family.radiusLeft horizontalMargin : Int) +
      family.baseTop 1 ≤ family.baseLeft 1 + verticalMargin)
    (hrightTop : (family.radiusRight horizontalMargin : Int) +
      family.baseTop 1 ≤ family.baseRight 1 + verticalMargin)
    (hbottomLeft : (family.radiusBottom verticalMargin : Int) +
      family.baseBottom 0 ≤ family.baseLeft 0 + horizontalMargin)
    (htopLeft : (family.radiusTop verticalMargin : Int) +
      family.baseTop 0 ≤ family.baseLeft 0 + horizontalMargin)
    (hbottomRight : (family.radiusBottom verticalMargin : Int) +
      family.baseRight 0 ≤ family.baseBottom 0 + horizontalMargin)
    (htopRight : (family.radiusTop verticalMargin : Int) +
      family.baseRight 0 ≤ family.baseTop 0 + horizontalMargin) :
    let gridBase : Site 2 := fun i ↦ if i = 0 then
      family.baseLeft 0 + horizontalMargin
    else family.baseBottom 1 + verticalMargin
    let b : Int := gridBase 0 + width -
      (family.baseRight 0 - horizontalMargin)
    let d : Int := gridBase 1 + height -
      (family.baseTop 1 - verticalMargin)
    ((family.radiusLeft horizontalMargin : Int) ≤ b) →
    ((family.radiusRight horizontalMargin : Int) ≤ b) →
    ((family.radiusBottom verticalMargin : Int) ≤ d) →
    ((family.radiusTop verticalMargin : Int) ≤ d) →
    (0 : Real) ≤ b ∧ (0 : Real) ≤ d ∧
    (∀ i : Fin (width + 1), p < mu.real
      (E.rectSideConnectionEvent 0 b 0 d
        (P.shift (gridBase + preferenceGridSite
          (i, (0 : Fin (height + 1)))) '' (S : Set V))
        (E.rectBottomBoundaryVertices 0 b 0 d))) ∧
    (∀ i : Fin (width + 1), p < mu.real
      (E.rectSideConnectionEvent 0 b 0 d
        (P.shift (gridBase + preferenceGridSite
          (i, Fin.last height)) '' (S : Set V))
        (E.rectTopBoundaryVertices 0 b 0 d))) ∧
    (∀ j : Fin (height + 1), p < mu.real
      (E.rectSideConnectionEvent 0 b 0 d
        (P.shift (gridBase + preferenceGridSite
          ((0 : Fin (width + 1)), j)) '' (S : Set V))
        (E.rectLeftBoundaryVertices 0 b 0 d))) ∧
    (∀ j : Fin (height + 1), p < mu.real
      (E.rectSideConnectionEvent 0 b 0 d
        (P.shift (gridBase + preferenceGridSite
          (Fin.last width, j)) '' (S : Set V))
        (E.rectRightBoundaryVertices 0 b 0 d))) := by
  dsimp only
  intro hbLeft hbRight hdBottom hdTop
  let gridBase : Site 2 := fun i ↦ if i = 0 then
    family.baseLeft 0 + horizontalMargin
  else family.baseBottom 1 + verticalMargin
  let b : Int := gridBase 0 + width -
    (family.baseRight 0 - horizontalMargin)
  let d : Int := gridBase 1 + height -
    (family.baseTop 1 - verticalMargin)
  have hmixed := family.mixedBoundaryScores E mu hTI
    horizontalMargin verticalMargin width height hleftBottom hrightBottom
    hbLeft hbRight hdBottom hdTop
  let bottomLower : Int := gridBase 0 - family.baseBottom 0 -
    family.radiusBottom verticalMargin
  let topLower : Int := gridBase 0 - family.baseTop 0 -
    family.radiusTop verticalMargin
  let bottomUpper : Int := gridBase 0 + width - family.baseBottom 0 +
    family.radiusBottom verticalMargin
  let topUpper : Int := gridBase 0 + width - family.baseTop 0 +
    family.radiusTop verticalMargin
  let leftUpper : Int := gridBase 1 + height - family.baseLeft 1 +
    family.radiusLeft horizontalMargin
  let rightUpper : Int := gridBase 1 + height - family.baseRight 1 +
    family.radiusRight horizontalMargin
  have hbottomLower : 0 ≤ bottomLower := by
    dsimp only [bottomLower, gridBase]
    simp only [if_pos, Fin.isValue]
    omega
  have htopLower : 0 ≤ topLower := by
    dsimp only [topLower, gridBase]
    simp only [if_pos, Fin.isValue]
    omega
  have hbottomUpper : bottomUpper ≤ b := by
    dsimp only [bottomUpper, b, gridBase]
    simp only [if_pos, Fin.isValue]
    omega
  have htopUpper : topUpper ≤ b := by
    dsimp only [topUpper, b, gridBase]
    simp only [if_pos, Fin.isValue]
    omega
  have hleftUpper : leftUpper ≤ d := by
    dsimp only [leftUpper, d, gridBase]
    simp only [if_neg (by decide : (1 : Fin 2) ≠ 0)]
    omega
  have hrightUpper : rightUpper ≤ d := by
    dsimp only [rightUpper, d, gridBase]
    simp only [if_neg (by decide : (1 : Fin 2) ≠ 0)]
    omega
  have ha : min 0 (min bottomLower topLower) = 0 := by
    simp [min_eq_left, hbottomLower, htopLower]
  have hb : max b (max bottomUpper topUpper) = b := by
    simp [max_eq_left, hbottomUpper, htopUpper]
  have hd : max d (max leftUpper rightUpper) = d := by
    simp [max_eq_left, hleftUpper, hrightUpper]
  have hb0 : (0 : Real) ≤ b := by
    have hr : (0 : Int) ≤ family.radiusLeft horizontalMargin := by omega
    exact_mod_cast hr.trans hbLeft
  have hd0 : (0 : Real) ≤ d := by
    have hr : (0 : Int) ≤ family.radiusBottom verticalMargin := by omega
    exact_mod_cast hr.trans hdBottom
  dsimp only [gridBase, b, d, bottomLower, topLower, bottomUpper,
    topUpper, leftUpper, rightUpper] at ha hb hd
  rw [ha, hb, hd] at hmixed
  refine ⟨hb0, hd0, ?_, ?_, ?_, ?_⟩
  · simpa only [gridBase, b, d, Int.cast_zero] using hmixed.2.1
  · simpa only [gridBase, b, d, Int.cast_zero] using hmixed.2.2.1
  · simpa only [gridBase, b, d, Int.cast_zero] using hmixed.2.2.2.1
  · simpa only [gridBase, b, d, Int.cast_zero] using hmixed.2.2.2.2


theorem PeriodicPlaneEmbedding.CommonSquareNormalBoundaryBandData.bottomBandScore
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {margin M : Nat} {p : Real}
    (data : E.CommonSquareNormalBoundaryBandData mu S margin M p)
    (width height : Nat) (v : PreferenceGridVertex width height)
    (hv : v.2.val ≤ margin) :
    p < mu.real (E.rectSideConnectionEvent
      (-(M : Real)) (M + width : Real)
      (-(M : Real)) (M + height : Real)
      ((P.fourShiftTemplate S data.zLeft data.zRight data.zBottom data.zTop).image
        (P.shift (preferenceGridSite v)) : Set V)
      (E.rectBottomBoundaryVertices (-(M : Real)) (M + width : Real)
        (-(M : Real)) (M + height : Real))) := by
  let j : Fin (margin + 1) := ⟨v.2.val, by omega⟩
  let t : Site 2 := verticalShift j.val
  have hle := E.rectBottomConnection_fourShiftTemplate_le mu hTI
    M width height S (data.zLeft + t) (data.zRight + t)
      (data.zBottom + t) (data.zTop + t) v.1
  have htarget :
      (P.fourShiftTemplate S (data.zLeft + t) (data.zRight + t)
          (data.zBottom + t) (data.zTop + t)).image
          (P.shift (preferenceGridSite
            (v.1, (0 : Fin (height + 1))))) =
        (P.fourShiftTemplate S data.zLeft data.zRight data.zBottom data.zTop).image
          (P.shift (preferenceGridSite v)) := by
    rw [P.fourShiftTemplate_add_image]
    congr 2
    apply congrArg P.shift
    funext k
    fin_cases k <;> simp [t, j, preferenceGridSite]
  rw [htarget] at hle
  have hscore := (data.bottom j).2
  have hscore' : p < mu.real (E.rectSideConnectionEvent
      (-(M : Real)) (M : Real) (-(M : Real)) (M : Real)
      (S.image (P.shift (data.zBottom + t)) : Set V)
      (E.rectBottomBoundaryVertices (-(M : Real)) (M : Real)
        (-(M : Real)) (M : Real))) := by
    simpa only [Finset.coe_image, t] using hscore
  exact hscore'.trans_le hle


theorem PeriodicPlaneEmbedding.CommonSquareNormalBoundaryBandData.topBandScore
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {margin M : Nat} {p : Real}
    (data : E.CommonSquareNormalBoundaryBandData mu S margin M p)
    (width height : Nat) (v : PreferenceGridVertex width height)
    (hv : height ≤ v.2.val + margin) :
    p < mu.real (E.rectSideConnectionEvent
      (-(M : Real)) (M + width : Real)
      (-(M : Real)) (M + height : Real)
      ((P.fourShiftTemplate S data.zLeft data.zRight data.zBottom data.zTop).image
        (P.shift (preferenceGridSite v)) : Set V)
      (E.rectTopBoundaryVertices (-(M : Real)) (M + width : Real)
        (-(M : Real)) (M + height : Real))) := by
  let k : Fin (margin + 1) := ⟨height - v.2.val, by omega⟩
  let t : Site 2 := verticalShift (-(k.val : Int))
  have hle := E.rectTopConnection_fourShiftTemplate_le mu hTI
    M width height S (data.zLeft + t) (data.zRight + t)
      (data.zBottom + t) (data.zTop + t) v.1
  have htarget :
      (P.fourShiftTemplate S (data.zLeft + t) (data.zRight + t)
          (data.zBottom + t) (data.zTop + t)).image
          (P.shift (preferenceGridSite (v.1, Fin.last height))) =
        (P.fourShiftTemplate S data.zLeft data.zRight data.zBottom data.zTop).image
          (P.shift (preferenceGridSite v)) := by
    rw [P.fourShiftTemplate_add_image]
    congr 2
    apply congrArg P.shift
    funext q
    fin_cases q <;> simp [t, k, preferenceGridSite] <;> omega
  rw [htarget] at hle
  have hscore := (data.top k).2
  have hscore' : p < mu.real (E.rectSideConnectionEvent
      (-(M : Real)) (M : Real) (-(M : Real)) (M : Real)
      (S.image (P.shift (data.zTop + t)) : Set V)
      (E.rectTopBoundaryVertices (-(M : Real)) (M : Real)
        (-(M : Real)) (M : Real))) := by
    simpa only [Finset.coe_image, t] using hscore
  exact hscore'.trans_le hle


theorem PeriodicPlaneEmbedding.CommonSquareNormalBoundaryBandData.leftBandScore
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {margin M : Nat} {p : Real}
    (data : E.CommonSquareNormalBoundaryBandData mu S margin M p)
    (width height : Nat) (v : PreferenceGridVertex width height)
    (hv : v.1.val ≤ margin) :
    p < mu.real (E.rectSideConnectionEvent
      (-(M : Real)) (M + width : Real)
      (-(M : Real)) (M + height : Real)
      ((P.fourShiftTemplate S data.zLeft data.zRight data.zBottom data.zTop).image
        (P.shift (preferenceGridSite v)) : Set V)
      (E.rectLeftBoundaryVertices (-(M : Real)) (M + width : Real)
        (-(M : Real)) (M + height : Real))) := by
  let i : Fin (margin + 1) := ⟨v.1.val, by omega⟩
  let t : Site 2 := horizontalShift i.val
  have hle := E.rectLeftConnection_fourShiftTemplate_le mu hTI
    M width height S (data.zLeft + t) (data.zRight + t)
      (data.zBottom + t) (data.zTop + t) v.2
  have htarget :
      (P.fourShiftTemplate S (data.zLeft + t) (data.zRight + t)
          (data.zBottom + t) (data.zTop + t)).image
          (P.shift (preferenceGridSite
            ((0 : Fin (width + 1)), v.2))) =
        (P.fourShiftTemplate S data.zLeft data.zRight data.zBottom data.zTop).image
          (P.shift (preferenceGridSite v)) := by
    rw [P.fourShiftTemplate_add_image]
    congr 2
    apply congrArg P.shift
    funext q
    fin_cases q <;> simp [t, i, preferenceGridSite]
  rw [htarget] at hle
  have hscore := (data.left i).2
  have hscore' : p < mu.real (E.rectSideConnectionEvent
      (-(M : Real)) (M : Real) (-(M : Real)) (M : Real)
      (S.image (P.shift (data.zLeft + t)) : Set V)
      (E.rectLeftBoundaryVertices (-(M : Real)) (M : Real)
        (-(M : Real)) (M : Real))) := by
    simpa only [Finset.coe_image, t] using hscore
  exact hscore'.trans_le hle


theorem PeriodicPlaneEmbedding.CommonSquareNormalBoundaryBandData.rightBandScore
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {margin M : Nat} {p : Real}
    (data : E.CommonSquareNormalBoundaryBandData mu S margin M p)
    (width height : Nat) (v : PreferenceGridVertex width height)
    (hv : width ≤ v.1.val + margin) :
    p < mu.real (E.rectSideConnectionEvent
      (-(M : Real)) (M + width : Real)
      (-(M : Real)) (M + height : Real)
      ((P.fourShiftTemplate S data.zLeft data.zRight data.zBottom data.zTop).image
        (P.shift (preferenceGridSite v)) : Set V)
      (E.rectRightBoundaryVertices (-(M : Real)) (M + width : Real)
        (-(M : Real)) (M + height : Real))) := by
  let k : Fin (margin + 1) := ⟨width - v.1.val, by omega⟩
  let t : Site 2 := horizontalShift (-(k.val : Int))
  have hle := E.rectRightConnection_fourShiftTemplate_le mu hTI
    M width height S (data.zLeft + t) (data.zRight + t)
      (data.zBottom + t) (data.zTop + t) v.2
  have htarget :
      (P.fourShiftTemplate S (data.zLeft + t) (data.zRight + t)
          (data.zBottom + t) (data.zTop + t)).image
          (P.shift (preferenceGridSite (Fin.last width, v.2))) =
        (P.fourShiftTemplate S data.zLeft data.zRight data.zBottom data.zTop).image
          (P.shift (preferenceGridSite v)) := by
    rw [P.fourShiftTemplate_add_image]
    congr 2
    apply congrArg P.shift
    funext q
    fin_cases q <;> simp [t, k, preferenceGridSite] <;> omega
  rw [htarget] at hle
  have hscore := (data.right k).2
  have hscore' : p < mu.real (E.rectSideConnectionEvent
      (-(M : Real)) (M : Real) (-(M : Real)) (M : Real)
      (S.image (P.shift (data.zRight + t)) : Set V)
      (E.rectRightBoundaryVertices (-(M : Real)) (M : Real)
        (-(M : Real)) (M : Real))) := by
    simpa only [Finset.coe_image, t] using hscore
  exact hscore'.trans_le hle


theorem PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_commonBoundaryBandScores
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (squareRequirement margin width height : Nat) :
    ∃ M, ∃ data : E.CommonSquareNormalBoundaryBandData mu S margin M p,
      squareRequirement ≤ M ∧
      (let template := P.fourShiftTemplate S data.zLeft data.zRight
        data.zBottom data.zTop
      (∀ v : PreferenceGridVertex width height,
        (template.image (P.shift (preferenceGridSite v)) : Set V) ⊆
          E.rectVertices (-(M : Real)) (M + width : Real)
            (-(M : Real)) (M + height : Real)) ∧
      (∀ v : PreferenceGridVertex width height, v.2.val ≤ margin →
        p < mu.real (E.rectSideConnectionEvent
          (-(M : Real)) (M + width : Real)
          (-(M : Real)) (M + height : Real)
          (template.image (P.shift (preferenceGridSite v)) : Set V)
          (E.rectBottomBoundaryVertices (-(M : Real)) (M + width : Real)
            (-(M : Real)) (M + height : Real)))) ∧
      (∀ v : PreferenceGridVertex width height,
        height ≤ v.2.val + margin →
        p < mu.real (E.rectSideConnectionEvent
          (-(M : Real)) (M + width : Real)
          (-(M : Real)) (M + height : Real)
          (template.image (P.shift (preferenceGridSite v)) : Set V)
          (E.rectTopBoundaryVertices (-(M : Real)) (M + width : Real)
            (-(M : Real)) (M + height : Real)))) ∧
      (∀ v : PreferenceGridVertex width height, v.1.val ≤ margin →
        p < mu.real (E.rectSideConnectionEvent
          (-(M : Real)) (M + width : Real)
          (-(M : Real)) (M + height : Real)
          (template.image (P.shift (preferenceGridSite v)) : Set V)
          (E.rectLeftBoundaryVertices (-(M : Real)) (M + width : Real)
            (-(M : Real)) (M + height : Real)))) ∧
      (∀ v : PreferenceGridVertex width height,
        width ≤ v.1.val + margin →
        p < mu.real (E.rectSideConnectionEvent
          (-(M : Real)) (M + width : Real)
          (-(M : Real)) (M + height : Real)
          (template.image (P.shift (preferenceGridSite v)) : Set V)
          (E.rectRightBoundaryVertices (-(M : Real)) (M + width : Real)
            (-(M : Real)) (M + height : Real))))) := by
  let seed := family.seed E margin
  let M := max squareRequirement (max (max seed.radiusLeft seed.radiusRight)
    (max seed.radiusBottom seed.radiusTop))
  have hrequirement : squareRequirement ≤ M := Nat.le_max_left _ _
  have hleft : seed.radiusLeft ≤ M :=
    ((Nat.le_max_left _ _).trans (Nat.le_max_left _ _)).trans
      (Nat.le_max_right _ _)
  have hright : seed.radiusRight ≤ M :=
    ((Nat.le_max_right _ _).trans (Nat.le_max_left _ _)).trans
      (Nat.le_max_right _ _)
  have hbottom : seed.radiusBottom ≤ M :=
    ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)).trans
      (Nat.le_max_right _ _)
  have htop : seed.radiusTop ≤ M :=
    ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)).trans
      (Nat.le_max_right _ _)
  let data := seed.toCommonSquare E mu hTI M hleft hright hbottom htop
  refine ⟨M, data, hrequirement, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    apply E.fourShiftTemplate_preferenceGrid_subset_rect
      M width height S data.zLeft data.zRight data.zBottom data.zTop
    · simpa [Finset.coe_image, horizontalShift] using
        (data.left (0 : Fin (margin + 1))).1
    · simpa [Finset.coe_image, horizontalShift] using
        (data.right (0 : Fin (margin + 1))).1
    · simpa [Finset.coe_image, verticalShift] using
        (data.bottom (0 : Fin (margin + 1))).1
    · simpa [Finset.coe_image, verticalShift] using
        (data.top (0 : Fin (margin + 1))).1
  · intro v hv
    exact data.bottomBandScore E mu hTI width height v hv
  · intro v hv
    exact data.topBandScore E mu hTI width height v hv
  · intro v hv
    exact data.leftBandScore E mu hTI width height v hv
  · intro v hv
    exact data.rightBandScore E mu hTI width height v hv


end StatMech.FK.PeriodicPlanar
