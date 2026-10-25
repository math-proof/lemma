/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part7
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

set_option linter.unusedVariables false in


theorem PeriodicPlaneEmbedding.uniformTemplateDeepGridAdjacentHeightCrossingRadius_of_pairMerge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (template : Nat -> Finset V)
    (htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1))
    (step : Nat -> Int) (hstep : forall n, 0 <= step n)
    (radius : Nat -> Nat)
    (hmerge : forall q : Nat -> Fin 2 × (Fin 3 × Fin 3),
      Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template n)
        ((template n).image (P.shift
          (preferenceKingOffset (q n).2 +
            if (q n).1.val = 0 then 0 else verticalShift (step n))))
        (radius n))) atTop (nhds 0)) :
    E.UniformTemplateDeepGridAdjacentHeightCrossingRadius
      mu template step radius := by
  classical
  let neighbor : Nat -> (Fin 2 × (Fin 3 × Fin 3)) -> Finset V := fun n q =>
    (template n).image (P.shift (preferenceKingOffset q.2 +
      if q.1.val = 0 then 0 else verticalShift (step n)))
  intro width height margin hwidth base vertical horizontal
    a b c d epsilon bottom top left right hepsilon hepsilon0
    hsource hconnector hbottomScore htopScore hleftScore hrightScore
    hVbottom hVtop hHleft hHright hVtrue hVfalse hHtrue hHfalse
  have hwitness (n : Nat) :=
    E.exists_deep_adjacentHeight_preference_crossing_branch
      mu hFKG hTI (a n) (b n) (c n) (d n) (step n) (hstep n)
      (hwidth n) (epsilon n) (hepsilon0 n)
      (fun v => (template n).image
        (P.shift (base n + preferenceGridSite v)))
      (bottom n) (top n) (left n) (right n)
      (vertical n) (horizontal n) (hsource n)
      (hbottomScore n) (htopScore n) (hleftScore n) (hrightScore n)
      (hVbottom n) (hVtop n) (hHleft n) (hHright n)
      (hVtrue n) (hVfalse n) (hHtrue n) (hHfalse n)
  choose x xVertical xHorizontal hxVadj hxHadj hxLeft hxRight
    hxBottom hxTop hbranch using hwitness
  choose ijV hijV using fun n =>
    exists_preferenceKingOffset_of_kingAdj (hxVadj n)
  choose ijH hijH using fun n =>
    exists_preferenceKingOffset_of_kingAdj (hxHadj n)
  let source : (n : Nat) ->
      PreferenceGridVertex (width n) (height n) -> Finset V := fun n v =>
    (template n).image (P.shift (base n + preferenceGridSite v))
  let shiftedVerticalSource : Nat -> Finset V := fun n =>
    (source n (xVertical n)).image (P.shift (verticalShift (step n)))
  let z : Nat -> Site 2 := fun n => base n + preferenceGridSite (x n)
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
  have hneighbor0 (n : Nat) (ij : Fin 3 × Fin 3) :
      (neighbor n ((0 : Fin 2), ij)).image (P.shift (z n)) =
        (template n).image
          (P.shift (z n + preferenceKingOffset ij)) := by
    simp only [neighbor, Fin.isValue, Fin.val_zero, if_pos, add_zero,
      Finset.image_image]
    apply Finset.image_congr
    intro u hu
    simpa [add_comm] using
      (P.shift_add (preferenceKingOffset ij) (z n) u).symm
  have hneighbor1 (n : Nat) (ij : Fin 3 × Fin 3) :
      (neighbor n ((1 : Fin 2), ij)).image (P.shift (z n)) =
        ((template n).image
          (P.shift (z n + preferenceKingOffset ij))).image
            (P.shift (verticalShift (step n))) := by
    simp only [neighbor, Fin.isValue, Fin.val_one, one_ne_zero, if_false,
      Finset.image_image]
    apply Finset.image_congr
    intro u hu
    change P.shift (z n)
        (P.shift (preferenceKingOffset ij + verticalShift (step n)) u) =
      P.shift (verticalShift (step n))
        (P.shift (z n + preferenceKingOffset ij) u)
    rw [<- P.shift_add, <- P.shift_add]
    congr 2
    abel
  have hrectZ (n : Nat) :
      (P.shift (z n) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
          E.rectVertices (a n) (b n) (c n) (d n) := by
    exact hconnector n (x n) (hxLeft n) (hxRight n)
      (hxBottom n) (hxTop n)
  have hrectHull (n : Nat) :
      (P.shift (z n) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
          E.rectVertices (a n) (b n) (c n) (d n + step n) := by
    have hstepR : (0 : Real) <= step n := by exact_mod_cast hstep n
    exact (hrectZ n).trans
      (E.rectVertices_mono le_rfl le_rfl le_rfl (by linarith))
  have hMv00 :=
    E.translated_rectanglePairMergeErrorUnion_tendsto_zero_of_pairMerge
      mu hTI template (fun n => neighbor n ((0 : Fin 2), ijV n))
      radius z a b c d hrectZ (by
        simpa only [neighbor] using
          hmerge (fun n => ((0 : Fin 2), ijV n)))
  have hMv10 :=
    E.translated_rectanglePairMergeErrorUnion_tendsto_zero_of_pairMerge
      mu hTI template (fun n => neighbor n ((1 : Fin 2), ijV n))
      radius z a b c (fun n => d n + step n) hrectHull (by
        simpa only [neighbor] using
          hmerge (fun n => ((1 : Fin 2), ijV n)))
  have hMh0 :=
    E.translated_rectanglePairMergeErrorUnion_tendsto_zero_of_pairMerge
      mu hTI template (fun n => neighbor n ((0 : Fin 2), ijH n))
      radius z a b c d hrectZ (by
        simpa only [neighbor] using
          hmerge (fun n => ((0 : Fin 2), ijH n)))
  let Mv0 : Nat -> Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n)
      (source n (x n)) (source n (xVertical n)))
  let Mv1 : Nat -> Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n + step n)
      (source n (x n)) (shiftedVerticalSource n))
  let Mv : Nat -> Real := fun n => Mv0 n + Mv1 n
  let Mh : Nat -> Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n)
      (source n (x n)) (source n (xHorizontal n)))
  have hMv0 : Tendsto Mv0 atTop (nhds 0) := by
    simpa only [Mv0, source, z, hneighbor0, hzV] using hMv00
  have hMv1 : Tendsto Mv1 atTop (nhds 0) := by
    simpa only [Mv1, source, shiftedVerticalSource, z, hneighbor1, hzV]
      using hMv10
  have hMv : Tendsto Mv atTop (nhds 0) := by
    simpa only [Mv, zero_add] using hMv0.add hMv1
  have hMh : Tendsto Mh atTop (nhds 0) := by
    simpa only [Mh, source, z, hneighbor0, hzH] using hMh0
  let verticalBranch : Nat -> Prop := fun n =>
    1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.setHitsInfinite (source n (x n) : Set V)))) <=
          bottom n (x n) + epsilon n /\
      bottom n (x n) *
          (mu.real (P.setHitsInfinite
              (source n (xVertical n) : Set V)) * bottom n (x n) -
            Mv0 n - epsilon n) - Mv1 n <=
        mu.real (E.verticalCrossingEvent
          (a n) (b n) (c n) (d n + step n))
  let A : Nat -> Real := fun n =>
    if verticalBranch n then bottom n (x n) else left n (x n)
  let Hv : Nat -> Real := fun n =>
    mu.real (P.setHitsInfinite (source n (xVertical n) : Set V))
  let Hh : Nat -> Real := fun n =>
    mu.real (P.setHitsInfinite (source n (xHorizontal n) : Set V))
  let Cv : Nat -> Real := fun n => mu.real
    (E.verticalCrossingEvent (a n) (b n) (c n) (d n + step n))
  let Ch : Nat -> Real := fun n => mu.real
    (E.horizontalCrossingEvent (a n) (b n) (c n) (d n))
  let root : Nat -> Real := fun n =>
    1 - Real.sqrt (Real.sqrt
      (1 - mu.real (P.setHitsInfinite (source n (x n) : Set V))))
  have htranslatedHit (q : (n : Nat) ->
      PreferenceGridVertex (width n) (height n)) : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (source n (q n) : Set V)))
      atTop (nhds 1) := by
    apply htemplateHit.congr'
    filter_upwards with n
    have hset : ((source n (q n) : Finset V) : Set V) =
        P.shift (base n + preferenceGridSite (q n)) ''
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
  have hrootA (n : Nat) : root n <= A n + epsilon n := by
    by_cases hv : verticalBranch n
    · simpa [A, root, hv] using hv.1
    · simpa [A, root, source, shiftedVerticalSource, Mv0, Mv1, hv] using
        ((hbranch n).resolve_left hv).1
  have hAupper (n : Nat) : A n <= 1 := by
    by_cases hv : verticalBranch n
    · simp only [A, if_pos hv]
      rw [hbottomScore n (x n)]
      exact measureReal_le_one
    · simp only [A, if_neg hv]
      rw [hleftScore n (x n)]
      exact measureReal_le_one
  have hcrossingBranch (n : Nat) :
      A n * (Hv n * A n - Mv n - epsilon n) - Mv n <= Cv n \/
      A n * (Hh n * A n - Mh n - epsilon n) - Mh n <= Ch n := by
    by_cases hv : verticalBranch n
    · left
      have hraw := hv.2
      have hA0 : 0 <= bottom n (x n) := by
        rw [hbottomScore]
        exact measureReal_nonneg
      have hM0 : 0 <= Mv0 n := measureReal_nonneg
      have hM1 : 0 <= Mv1 n := measureReal_nonneg
      simp only [A, if_pos hv, Hv, Cv, Mv] at ⊢
      nlinarith
    · right
      have hb := (hbranch n).resolve_left hv
      simpa [A, Hh, Ch, Mh, source, shiftedVerticalSource, Mv0, Mv1, hv]
        using hb.2
  simpa [Cv, Ch, max_comm] using
    crossing_max_tendsto_one_of_approxPreferredSide_root_branches
      root A Hv Hh Mv Mh epsilon Cv Ch hroot hrootA hAupper
      hHv hHh hMv hMh hepsilon hcrossingBranch
      (fun _ => measureReal_le_one) (fun _ => measureReal_le_one)


theorem PeriodicPlaneEmbedding.exists_uniformTemplate_deepGrid_adjacentHeight_crossing_max_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (template : Nat -> Finset V)
    (htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1))
    (step : Nat -> Int) (hstep : forall n, 0 <= step n) :
    exists radius : Nat -> Nat,
      E.UniformTemplateDeepGridAdjacentHeightCrossingRadius
        mu template step radius := by
  let neighbor : Nat -> (Fin 2 × (Fin 3 × Fin 3)) -> Finset V := fun n q =>
    (template n).image (P.shift (preferenceKingOffset q.2 +
      if q.1.val = 0 then 0 else verticalShift (step n)))
  obtain ⟨radius, hradius⟩ :=
    P.exists_uniform_pairMergeRadius mu hunique template neighbor
  have hepsilon : Tendsto (fun n : Nat => (1 : Real) / (n + 1))
      atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hmerge (q : Nat -> Fin 2 × (Fin 3 × Fin 3)) :
      Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template n)
        ((template n).image (P.shift
          (preferenceKingOffset (q n).2 +
            if (q n).1.val = 0 then 0 else verticalShift (step n))))
        (radius n))) atTop (nhds 0) := by
    exact squeeze_zero (fun _ => measureReal_nonneg)
      (fun n => le_of_lt ((hradius n).2 (q n))) hepsilon
  exact ⟨radius,
    E.uniformTemplateDeepGridAdjacentHeightCrossingRadius_of_pairMerge
      mu hFKG hTI template htemplateHit step hstep radius hmerge⟩


theorem PeriodicPlaneEmbedding.exists_adjacentHeight_pairMergeRadius_at_error
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (template : Finset V) (step : Int) (cutoff : Nat)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    exists radius : Nat, cutoff <= radius /\
      forall q : Fin 2 × (Fin 3 × Fin 3),
        mu.real (P.pairMergeErrorUnion template
          (template.image (P.shift (preferenceKingOffset q.2 +
            if q.1.val = 0 then 0 else verticalShift step))) radius) <
          epsilon := by
  let neighbor : Fin 2 × (Fin 3 × Fin 3) -> Finset V := fun q =>
    template.image (P.shift (preferenceKingOffset q.2 +
      if q.1.val = 0 then 0 else verticalShift step))
  have hsum : Tendsto (fun radius =>
      ∑ q : Fin 2 × (Fin 3 × Fin 3),
        mu.real (P.pairMergeErrorUnion template (neighbor q) radius))
      atTop (nhds 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun q _ =>
      P.pairMergeErrorUnion_real_tendsto_zero
        mu hunique template (neighbor q))
  rw [Metric.tendsto_atTop] at hsum
  obtain ⟨threshold, hthreshold⟩ := hsum epsilon hepsilon
  let radius := max cutoff threshold
  have htotal : (∑ q : Fin 2 × (Fin 3 × Fin 3),
      mu.real (P.pairMergeErrorUnion template (neighbor q) radius)) <
      epsilon := by
    simpa [Real.dist_eq, abs_of_nonneg (Finset.sum_nonneg fun _ _ =>
      measureReal_nonneg)] using
      hthreshold radius (Nat.le_max_right cutoff threshold)
  refine ⟨radius, Nat.le_max_left _ _, ?_⟩
  intro q
  change mu.real
      (P.pairMergeErrorUnion template (neighbor q) radius) < epsilon
  exact (Finset.single_le_sum
    (f := fun i : Fin 2 × (Fin 3 × Fin 3) =>
      mu.real (P.pairMergeErrorUnion template (neighbor i) radius))
    (fun i (_ : i ∈ Finset.univ) => measureReal_nonneg)
    (Finset.mem_univ q)).trans_lt htotal


theorem exists_radiusFirst_adjacentEndpointRow
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (template : Finset V) (step : Int) (cutoff : Nat)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (B r y s : Real) (hB0 : 0 <= B)
    (hB : forall {x z : W} (hxz : Pdual.graph.Adj x z)
      (u) (i : Fin 2),
      |Edual.coordinates (Edual.edgeArc hxz u - Edual.vertex x) i| <= B)
    (t : Int) (ht : 3 * B < t)
    (minimumWidth minimumHeight : Nat -> Nat)
    (horizontalLeft horizontalRight : Nat -> Int)
    (hhorizontalSpan : forall radius w,
      minimumWidth radius <= w ->
      3 * B < horizontalRight w - horizontalLeft w) :
    exists radius width height : Nat,
      cutoff <= radius /\
      minimumWidth radius <= width /\
      minimumHeight radius <= height /\
      (forall q : Fin 2 × (Fin 3 × Fin 3),
        mu.real (P.pairMergeErrorUnion template
          (template.image (P.shift (preferenceKingOffset q.2 +
            if q.1.val = 0 then 0 else verticalShift step))) radius) <
          epsilon) /\
      1 - epsilon < muDual.real (Edual.verticalCrossingEvent
        r (r + width) ((2 * s + (s + t)) / 3)
          ((s + 2 * (s + t)) / 3)) /\
      1 - epsilon < muDual.real (Edual.horizontalCrossingEvent
        (horizontalLeft width) (horizontalRight width)
        y (y + height)) := by
  obtain ⟨radius, hradius, hmerge⟩ :=
    E.exists_adjacentHeight_pairMergeRadius_at_error
      mu hunique template step cutoff epsilon hepsilon
  obtain ⟨width, hwidth, hvertical⟩ :=
    Edual.exists_verticalCrossing_measureReal_gt_of_unique
      muDual hFKGDual hTIDual huniqueDual r B s hB0 hB t ht
        (minimumWidth radius) hepsilon
  let horizontalS : Real := 2 * horizontalLeft width - horizontalRight width
  let horizontalT : Int :=
    3 * (horizontalRight width - horizontalLeft width)
  have hhorizontalT : 3 * B < horizontalT := by
    have hspan := hhorizontalSpan radius width hwidth
    rw [show (horizontalT : Real) =
        3 * ((horizontalRight width : Real) - horizontalLeft width) by
      simp only [horizontalT, Int.cast_mul, Int.cast_ofNat, Int.cast_sub]]
    nlinarith
  obtain ⟨height, hheight, hhorizontal⟩ :=
    Edual.exists_horizontalCrossing_measureReal_gt_of_unique
      muDual hFKGDual hTIDual huniqueDual y B horizontalS hB0 hB
        horizontalT hhorizontalT (minimumHeight radius) hepsilon
  refine ⟨radius, width, height, hradius, hwidth, hheight,
    hmerge, hvertical, ?_⟩
  convert hhorizontal using 1 <;>
    simp only [horizontalS, horizontalT, Int.cast_mul,
      Int.cast_ofNat, Int.cast_sub] <;> ring


theorem exists_radiusFirst_dependentGeometry_adjacentEndpointRow
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (template : Finset V) (step : Int) (cutoff : Nat)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (B : Real) (hB0 : 0 <= B)
    (hB : forall {x z : W} (hxz : Pdual.graph.Adj x z)
      (u) (i : Fin 2),
      |Edual.coordinates (Edual.edgeArc hxz u - Edual.vertex x) i| <= B)
    (r y s : Nat -> Real) (t : Nat -> Int)
    (ht : forall radius, 3 * B < t radius)
    (minimumWidth minimumHeight : Nat -> Nat)
    (horizontalLeft horizontalRight : Nat -> Nat -> Int)
    (hhorizontalSpan : forall radius w,
      minimumWidth radius <= w ->
      3 * B < horizontalRight radius w - horizontalLeft radius w) :
    exists radius width height : Nat,
      cutoff <= radius /\
      minimumWidth radius <= width /\
      minimumHeight radius <= height /\
      (forall q : Fin 2 × (Fin 3 × Fin 3),
        mu.real (P.pairMergeErrorUnion template
          (template.image (P.shift (preferenceKingOffset q.2 +
            if q.1.val = 0 then 0 else verticalShift step))) radius) <
          epsilon) /\
      1 - epsilon < muDual.real (Edual.verticalCrossingEvent
        (r radius) (r radius + width)
        ((2 * s radius + (s radius + t radius)) / 3)
        ((s radius + 2 * (s radius + t radius)) / 3)) /\
      1 - epsilon < muDual.real (Edual.horizontalCrossingEvent
        (horizontalLeft radius width) (horizontalRight radius width)
        (y radius) (y radius + height)) := by
  obtain ⟨radius, hradius, hmerge⟩ :=
    E.exists_adjacentHeight_pairMergeRadius_at_error
      mu hunique template step cutoff epsilon hepsilon
  obtain ⟨width, hwidth, hvertical⟩ :=
    Edual.exists_verticalCrossing_measureReal_gt_of_unique
      muDual hFKGDual hTIDual huniqueDual (r radius) B (s radius)
      hB0 hB (t radius) (ht radius) (minimumWidth radius) hepsilon
  let horizontalS : Real :=
    2 * horizontalLeft radius width - horizontalRight radius width
  let horizontalT : Int :=
    3 * (horizontalRight radius width - horizontalLeft radius width)
  have hhorizontalT : 3 * B < horizontalT := by
    have hspan := hhorizontalSpan radius width hwidth
    rw [show (horizontalT : Real) =
        3 * ((horizontalRight radius width : Real) -
          horizontalLeft radius width) by
      simp only [horizontalT, Int.cast_mul, Int.cast_ofNat, Int.cast_sub]]
    nlinarith
  obtain ⟨height, hheight, hhorizontal⟩ :=
    Edual.exists_horizontalCrossing_measureReal_gt_of_unique
      muDual hFKGDual hTIDual huniqueDual (y radius) B horizontalS
      hB0 hB horizontalT hhorizontalT (minimumHeight radius) hepsilon
  refine ⟨radius, width, height, hradius, hwidth, hheight,
    hmerge, hvertical, ?_⟩
  convert hhorizontal using 1 <;>
    simp only [horizontalS, horizontalT, Int.cast_mul,
      Int.cast_ofNat, Int.cast_sub] <;> ring


end StatMech.FK.PeriodicPlanar
