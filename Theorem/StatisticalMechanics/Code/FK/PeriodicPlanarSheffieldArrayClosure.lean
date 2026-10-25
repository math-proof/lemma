/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldMacroArrayAssembly.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

@[simp] theorem horizontalShift_zero_vector : horizontalShift 0 = 0 := by
  funext i
  fin_cases i <;> simp

@[simp] theorem verticalShift_zero_vector : verticalShift 0 = 0 := by
  funext i
  fin_cases i <;> simp

omit [Countable V] in


theorem PeriodicPlaneEmbedding.rectSideConnectionEvent_union_source
    (E : PeriodicPlaneEmbedding P) (a b c d : Real)
    (S T side : Set V) :
    E.rectSideConnectionEvent a b c d (S ∪ T) side =
      E.rectSideConnectionEvent a b c d S side ∪
        E.rectSideConnectionEvent a b c d T side := by
  ext omega
  constructor
  · rintro ⟨x, hx, hxInfinite, y, hy, hxy⟩
    rcases hx with hxS | hxT
    · exact Or.inl ⟨x, hxS, hxInfinite, y, hy, hxy⟩
    · exact Or.inr ⟨x, hxT, hxInfinite, y, hy, hxy⟩
  · rintro (hS | hT)
    · obtain ⟨x, hx, hxInfinite, y, hy, hxy⟩ := hS
      exact ⟨x, Or.inl hx, hxInfinite, y, hy, hxy⟩
    · obtain ⟨x, hx, hxInfinite, y, hy, hxy⟩ := hT
      exact ⟨x, Or.inr hx, hxInfinite, y, hy, hxy⟩

omit [Countable V] in


theorem PeriodicGraph.fourShiftTemplate_add
    (P : PeriodicGraph V) (S : Finset V)
    (zLeft zRight zBottom zTop t : Site 2) :
    P.fourShiftTemplate S (zLeft + t) (zRight + t)
        (zBottom + t) (zTop + t) =
      (P.fourShiftTemplate S zLeft zRight zBottom zTop).image (P.shift t) := by
  ext x
  simp only [PeriodicGraph.fourShiftTemplate, Finset.mem_union,
    Finset.mem_image]
  constructor
  · rintro ((⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) |
      (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩))
    · exact ⟨P.shift zLeft u, Or.inl (Or.inl ⟨u, hu, rfl⟩),
        (P.shift_add zLeft t u).symm⟩
    · exact ⟨P.shift zRight u, Or.inl (Or.inr ⟨u, hu, rfl⟩),
        (P.shift_add zRight t u).symm⟩
    · exact ⟨P.shift zBottom u, Or.inr (Or.inl ⟨u, hu, rfl⟩),
        (P.shift_add zBottom t u).symm⟩
    · exact ⟨P.shift zTop u, Or.inr (Or.inr ⟨u, hu, rfl⟩),
        (P.shift_add zTop t u).symm⟩
  · rintro ⟨y, ((⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) |
        (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)), rfl⟩
    · exact Or.inl (Or.inl ⟨u, hu, by
        exact P.shift_add zLeft t u⟩)
    · exact Or.inl (Or.inr ⟨u, hu, by
        exact P.shift_add zRight t u⟩)
    · exact Or.inr (Or.inl ⟨u, hu, by
        exact P.shift_add zBottom t u⟩)
    · exact Or.inr (Or.inr ⟨u, hu, by
        exact P.shift_add zTop t u⟩)

omit [Countable V] in
theorem PeriodicGraph.fourShiftTemplate_add_image
    (P : PeriodicGraph V) (S : Finset V)
    (zLeft zRight zBottom zTop t w : Site 2) :
    (P.fourShiftTemplate S (zLeft + t) (zRight + t)
        (zBottom + t) (zTop + t)).image (P.shift w) =
      (P.fourShiftTemplate S zLeft zRight zBottom zTop).image
        (P.shift (t + w)) := by
  rw [P.fourShiftTemplate_add, Finset.image_image]
  congr 1
  funext x
  exact (P.shift_add t w x).symm


theorem PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_mono_rectangle
    (E : PeriodicPlaneEmbedding P)
    {a b c d a' b' c' d' : Real} (L R : Finset V)
    (ha : a' ≤ a) (hb : b ≤ b') (hc : c' ≤ c) (hd : d ≤ d') :
    E.rectanglePairMergeErrorUnion a' b' c' d' L R ⊆
      E.rectanglePairMergeErrorUnion a b c d L R := by
  intro omega homega
  obtain ⟨x, hxL, y, hyR, hinfinite, hnotLarge⟩ := by
    simpa only [PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion,
      Set.mem_iUnion, Set.mem_diff, Set.mem_inter_iff,
      Set.mem_setOf_eq] using homega
  simp only [PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion,
    Set.mem_iUnion, Set.mem_diff, Set.mem_inter_iff, Set.mem_setOf_eq]
  refine ⟨x, hxL, y, hyR, hinfinite, ?_⟩
  intro hsmall
  exact hnotLarge (P.connectedWithinSet_mono_region
    (E.rectVertices_mono ha hb hc hd) x y hsmall)


theorem PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_measureReal_mono_rectangle
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    {a b c d a' b' c' d' : Real} (L R : Finset V)
    (ha : a' ≤ a) (hb : b ≤ b') (hc : c' ≤ c) (hd : d ≤ d') :
    mu.real (E.rectanglePairMergeErrorUnion a' b' c' d' L R) ≤
      mu.real (E.rectanglePairMergeErrorUnion a b c d L R) :=
  measureReal_mono
    (E.rectanglePairMergeErrorUnion_mono_rectangle L R ha hb hc hd)


theorem PeriodicPlaneEmbedding.rectBottomConnection_component_le_template_of_enlarge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    {a b c d a' b' d' : Real} (component template : Finset V)
    (hcomponent : component ⊆ template)
    (ha : a' ≤ a) (hb : b ≤ b') (hd : d ≤ d') :
    mu.real (E.rectSideConnectionEvent a b c d (component : Set V)
        (E.rectBottomBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a' b' c d' (template : Set V)
        (E.rectBottomBoundaryVertices a' b' c d')) := by
  apply measureReal_mono (h₂ := measure_ne_top mu _)
  exact (E.rectBottomConnectionEvent_mono_otherBounds
    (component : Set V) ha hb hd).trans
      (E.rectSideConnectionEvent_mono_source (by exact_mod_cast hcomponent))


theorem PeriodicPlaneEmbedding.rectTopConnection_component_le_template_of_enlarge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    {a b c d a' b' c' : Real} (component template : Finset V)
    (hcomponent : component ⊆ template)
    (ha : a' ≤ a) (hb : b ≤ b') (hc : c' ≤ c) :
    mu.real (E.rectSideConnectionEvent a b c d (component : Set V)
        (E.rectTopBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a' b' c' d (template : Set V)
        (E.rectTopBoundaryVertices a' b' c' d)) := by
  apply measureReal_mono (h₂ := measure_ne_top mu _)
  exact (E.rectTopConnectionEvent_mono_otherBounds
    (component : Set V) ha hb hc).trans
      (E.rectSideConnectionEvent_mono_source (by exact_mod_cast hcomponent))


theorem PeriodicPlaneEmbedding.rectLeftConnection_component_le_template_of_enlarge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    {a b c d b' c' d' : Real} (component template : Finset V)
    (hcomponent : component ⊆ template)
    (hb : b ≤ b') (hc : c' ≤ c) (hd : d ≤ d') :
    mu.real (E.rectSideConnectionEvent a b c d (component : Set V)
        (E.rectLeftBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b' c' d' (template : Set V)
        (E.rectLeftBoundaryVertices a b' c' d')) := by
  apply measureReal_mono (h₂ := measure_ne_top mu _)
  exact (E.rectLeftConnectionEvent_mono_otherBounds
    (component : Set V) hb hc hd).trans
      (E.rectSideConnectionEvent_mono_source (by exact_mod_cast hcomponent))


theorem PeriodicPlaneEmbedding.rectRightConnection_component_le_template_of_enlarge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    {a b c d a' c' d' : Real} (component template : Finset V)
    (hcomponent : component ⊆ template)
    (ha : a' ≤ a) (hc : c' ≤ c) (hd : d ≤ d') :
    mu.real (E.rectSideConnectionEvent a b c d (component : Set V)
        (E.rectRightBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a' b c' d' (template : Set V)
        (E.rectRightBoundaryVertices a' b c' d')) := by
  apply measureReal_mono (h₂ := measure_ne_top mu _)
  exact (E.rectRightConnectionEvent_mono_otherBounds
    (component : Set V) ha hc hd).trans
      (E.rectSideConnectionEvent_mono_source (by exact_mod_cast hcomponent))


theorem PeriodicPlaneEmbedding.verticalCrossing_ge_carriedComponents
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (a b c d : Real) (L R : Finset V)
    (aBottom bBottom dBottom aTop bTop cTop : Real)
    (aMerge bMerge cMerge dMerge : Real)
    (hBottomA : a ≤ aBottom) (hBottomB : bBottom ≤ b)
    (hBottomD : dBottom ≤ d)
    (hTopA : a ≤ aTop) (hTopB : bTop ≤ b) (hTopC : c ≤ cTop)
    (hMergeA : a ≤ aMerge) (hMergeB : bMerge ≤ b)
    (hMergeC : c ≤ cMerge) (hMergeD : dMerge ≤ d) :
    mu.real (E.rectSideConnectionEvent
        aBottom bBottom c dBottom (L : Set V)
        (E.rectBottomBoundaryVertices aBottom bBottom c dBottom)) *
      mu.real (E.rectSideConnectionEvent
        aTop bTop cTop d (R : Set V)
        (E.rectTopBoundaryVertices aTop bTop cTop d)) -
      mu.real (E.rectanglePairMergeErrorUnion
        aMerge bMerge cMerge dMerge L R) ≤
        mu.real (E.verticalCrossingEvent a b c d) := by
  have hBottom : mu.real (E.rectSideConnectionEvent
      aBottom bBottom c dBottom (L : Set V)
      (E.rectBottomBoundaryVertices aBottom bBottom c dBottom)) ≤
      mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
        (E.rectBottomBoundaryVertices a b c d)) :=
    measureReal_mono (h₂ := measure_ne_top mu _)
      (E.rectBottomConnectionEvent_mono_otherBounds
        (L : Set V) hBottomA hBottomB hBottomD)
  have hTop : mu.real (E.rectSideConnectionEvent
      aTop bTop cTop d (R : Set V)
      (E.rectTopBoundaryVertices aTop bTop cTop d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
        (E.rectTopBoundaryVertices a b c d)) :=
    measureReal_mono (h₂ := measure_ne_top mu _)
      (E.rectTopConnectionEvent_mono_otherBounds
        (R : Set V) hTopA hTopB hTopC)
  have hMerge :=
    E.rectanglePairMergeErrorUnion_measureReal_mono_rectangle
      mu L R hMergeA hMergeB hMergeC hMergeD
  have hProduct :
      mu.real (E.rectSideConnectionEvent
          aBottom bBottom c dBottom (L : Set V)
          (E.rectBottomBoundaryVertices aBottom bBottom c dBottom)) *
        mu.real (E.rectSideConnectionEvent
          aTop bTop cTop d (R : Set V)
          (E.rectTopBoundaryVertices aTop bTop cTop d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
          (E.rectBottomBoundaryVertices a b c d)) *
        mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
          (E.rectTopBoundaryVertices a b c d)) :=
    mul_le_mul hBottom hTop measureReal_nonneg measureReal_nonneg
  calc
    _ ≤ mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
            (E.rectBottomBoundaryVertices a b c d)) *
          mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
            (E.rectTopBoundaryVertices a b c d)) -
          mu.real (E.rectanglePairMergeErrorUnion a b c d L R) := by
      linarith
    _ ≤ mu.real (E.verticalCrossingEvent a b c d) :=
      E.verticalCrossing_measureReal_ge_side_mul_sub_mergeError
        mu hFKG a b c d L R


theorem PeriodicPlaneEmbedding.horizontalCrossing_ge_carriedComponents
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (a b c d : Real) (L R : Finset V)
    (bLeft cLeft dLeft aRight cRight dRight : Real)
    (aMerge bMerge cMerge dMerge : Real)
    (hLeftB : bLeft ≤ b) (hLeftC : c ≤ cLeft) (hLeftD : dLeft ≤ d)
    (hRightA : a ≤ aRight) (hRightC : c ≤ cRight)
    (hRightD : dRight ≤ d)
    (hMergeA : a ≤ aMerge) (hMergeB : bMerge ≤ b)
    (hMergeC : c ≤ cMerge) (hMergeD : dMerge ≤ d) :
    mu.real (E.rectSideConnectionEvent
        a bLeft cLeft dLeft (L : Set V)
        (E.rectLeftBoundaryVertices a bLeft cLeft dLeft)) *
      mu.real (E.rectSideConnectionEvent
        aRight b cRight dRight (R : Set V)
        (E.rectRightBoundaryVertices aRight b cRight dRight)) -
      mu.real (E.rectanglePairMergeErrorUnion
        aMerge bMerge cMerge dMerge L R) ≤
        mu.real (E.horizontalCrossingEvent a b c d) := by
  have hLeft : mu.real (E.rectSideConnectionEvent
      a bLeft cLeft dLeft (L : Set V)
      (E.rectLeftBoundaryVertices a bLeft cLeft dLeft)) ≤
      mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
        (E.rectLeftBoundaryVertices a b c d)) :=
    measureReal_mono (h₂ := measure_ne_top mu _)
      (E.rectLeftConnectionEvent_mono_otherBounds
        (L : Set V) hLeftB hLeftC hLeftD)
  have hRight : mu.real (E.rectSideConnectionEvent
      aRight b cRight dRight (R : Set V)
      (E.rectRightBoundaryVertices aRight b cRight dRight)) ≤
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
        (E.rectRightBoundaryVertices a b c d)) :=
    measureReal_mono (h₂ := measure_ne_top mu _)
      (E.rectRightConnectionEvent_mono_otherBounds
        (R : Set V) hRightA hRightC hRightD)
  have hMerge :=
    E.rectanglePairMergeErrorUnion_measureReal_mono_rectangle
      mu L R hMergeA hMergeB hMergeC hMergeD
  have hProduct :
      mu.real (E.rectSideConnectionEvent
          a bLeft cLeft dLeft (L : Set V)
          (E.rectLeftBoundaryVertices a bLeft cLeft dLeft)) *
        mu.real (E.rectSideConnectionEvent
          aRight b cRight dRight (R : Set V)
          (E.rectRightBoundaryVertices aRight b cRight dRight)) ≤
      mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
          (E.rectLeftBoundaryVertices a b c d)) *
        mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
          (E.rectRightBoundaryVertices a b c d)) :=
    mul_le_mul hLeft hRight measureReal_nonneg measureReal_nonneg
  calc
    _ ≤ mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
            (E.rectLeftBoundaryVertices a b c d)) *
          mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
            (E.rectRightBoundaryVertices a b c d)) -
          mu.real (E.rectanglePairMergeErrorUnion a b c d L R) := by
      linarith
    _ ≤ mu.real (E.horizontalCrossingEvent a b c d) :=
      E.horizontalCrossing_measureReal_ge_side_mul_sub_mergeError
        mu hFKG a b c d L R


theorem PeriodicPlaneEmbedding.verticalCrossing_ge_carriedComponents_of_connector
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu)
    (a b c d a' b' : Real) (bottom top : Finset V) (radius : Nat)
    (ha : a' ≤ a) (hb : b ≤ b')
    (hbox : (P.orbitBox (P.bufferedRadius radius) : Set V) ⊆
      E.rectVertices a' b' c d) :
    mu.real (E.rectSideConnectionEvent a b c d (bottom : Set V)
        (E.rectBottomBoundaryVertices a b c d)) *
      mu.real (E.rectSideConnectionEvent a b c d (top : Set V)
        (E.rectTopBoundaryVertices a b c d)) -
      mu.real (P.pairMergeErrorUnion bottom top radius) ≤
        mu.real (E.verticalCrossingEvent a' b' c d) := by
  have hrectangle := E.verticalCrossing_ge_carriedComponents mu hFKG
    a' b' c d bottom top a b d a b c a' b' c d
    ha hb le_rfl ha hb le_rfl le_rfl le_rfl le_rfl le_rfl
  have hmerge := E.rectanglePairMergeErrorUnion_measureReal_le
    mu a' b' c d bottom top radius hbox
  linarith


theorem PeriodicPlaneEmbedding.horizontalCrossing_ge_carriedComponents_of_connector
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu)
    (a b c d c' d' : Real) (left right : Finset V) (radius : Nat)
    (hc : c' ≤ c) (hd : d ≤ d')
    (hbox : (P.orbitBox (P.bufferedRadius radius) : Set V) ⊆
      E.rectVertices a b c' d') :
    mu.real (E.rectSideConnectionEvent a b c d (left : Set V)
        (E.rectLeftBoundaryVertices a b c d)) *
      mu.real (E.rectSideConnectionEvent a b c d (right : Set V)
        (E.rectRightBoundaryVertices a b c d)) -
      mu.real (P.pairMergeErrorUnion left right radius) ≤
        mu.real (E.horizontalCrossingEvent a b c' d') := by
  have hrectangle := E.horizontalCrossing_ge_carriedComponents mu hFKG
    a b c' d' left right b c d a c d a b c' d'
    le_rfl hc hd le_rfl hc hd le_rfl le_rfl le_rfl le_rfl
  have hmerge := E.rectanglePairMergeErrorUnion_measureReal_le
    mu a b c' d' left right radius hbox
  linarith


theorem PeriodicPlaneEmbedding.verticalCrossing_tendsto_one_of_carriedComponents
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu)
    (a b c d a' b' : Nat → Real)
    (bottom top : Nat → Finset V) (radius : Nat → Nat)
    (ha : ∀ n, a' n ≤ a n) (hb : ∀ n, b n ≤ b' n)
    (hbox : ∀ n,
      (P.orbitBox (P.bufferedRadius (radius n)) : Set V) ⊆
        E.rectVertices (a' n) (b' n) (c n) (d n))
    (hbottom : Tendsto (fun n ↦ mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        (bottom n : Set V)
        (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n))))
      atTop (nhds 1))
    (htop : Tendsto (fun n ↦ mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        (top n : Set V)
        (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n))))
      atTop (nhds 1))
    (hmerge : Tendsto (fun n ↦ mu.real
      (P.pairMergeErrorUnion (bottom n) (top n) (radius n)))
      atTop (nhds 0)) :
    Tendsto (fun n ↦ mu.real
      (E.verticalCrossingEvent (a' n) (b' n) (c n) (d n)))
      atTop (nhds 1) := by
  have hlower (n : Nat) :=
    E.verticalCrossing_ge_carriedComponents_of_connector mu hFKG
      (a n) (b n) (c n) (d n) (a' n) (b' n)
      (bottom n) (top n) (radius n) (ha n) (hb n) (hbox n)
  have hlimit := hbottom.mul htop |>.sub hmerge
  have hlimit' : Tendsto (fun n ↦
      mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          (bottom n : Set V)
          (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n))) *
        mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          (top n : Set V)
          (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n))) -
        mu.real (P.pairMergeErrorUnion (bottom n) (top n) (radius n)))
      atTop (nhds 1) := by
    convert hlimit using 1 <;> norm_num
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hlimit' tendsto_const_nhds hlower (fun _ ↦ measureReal_le_one)


theorem PeriodicPlaneEmbedding.horizontalCrossing_tendsto_one_of_carriedComponents
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu)
    (a b c d c' d' : Nat → Real)
    (left right : Nat → Finset V) (radius : Nat → Nat)
    (hc : ∀ n, c' n ≤ c n) (hd : ∀ n, d n ≤ d' n)
    (hbox : ∀ n,
      (P.orbitBox (P.bufferedRadius (radius n)) : Set V) ⊆
        E.rectVertices (a n) (b n) (c' n) (d' n))
    (hleft : Tendsto (fun n ↦ mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        (left n : Set V)
        (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n))))
      atTop (nhds 1))
    (hright : Tendsto (fun n ↦ mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        (right n : Set V)
        (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n))))
      atTop (nhds 1))
    (hmerge : Tendsto (fun n ↦ mu.real
      (P.pairMergeErrorUnion (left n) (right n) (radius n)))
      atTop (nhds 0)) :
    Tendsto (fun n ↦ mu.real
      (E.horizontalCrossingEvent (a n) (b n) (c' n) (d' n)))
      atTop (nhds 1) := by
  have hlower (n : Nat) :=
    E.horizontalCrossing_ge_carriedComponents_of_connector mu hFKG
      (a n) (b n) (c n) (d n) (c' n) (d' n)
      (left n) (right n) (radius n) (hc n) (hd n) (hbox n)
  have hlimit := hleft.mul hright |>.sub hmerge
  have hlimit' : Tendsto (fun n ↦
      mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          (left n : Set V)
          (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n))) *
        mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          (right n : Set V)
          (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n))) -
        mu.real (P.pairMergeErrorUnion (left n) (right n) (radius n)))
      atTop (nhds 1) := by
    convert hlimit using 1 <;> norm_num
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hlimit' tendsto_const_nhds hlower (fun _ ↦ measureReal_le_one)


end StatMech.FK.PeriodicPlanar
