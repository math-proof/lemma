/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part27
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem exists_carriedAsymmetricEndpointCoordinates_with_radius_requirements
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (B : Nat) (hBpos : 0 < B)
    (hB : forall {x z : W} (hxz : Pdual.graph.Adj x z)
      (u) (i : Fin 2),
      |Edual.coordinates (Edual.edgeArc hxz u - Edual.vertex x) i| <= B)
    (template : Nat -> Finset V)
    (minimumWidth targetY : Nat -> Nat -> Nat)
    (hminimumWidth : forall n radius,
      3 * B + 1 <= minimumWidth n radius)
    (htargetY : forall n radius, 20 * B + 1 <= targetY n radius) :
    exists radius width height : Nat -> Nat,
      Tendsto radius atTop atTop /\
      (forall n, minimumWidth n (radius n) <= width n) /\
      (forall q : Nat -> Fin 2 × (Fin 3 × Fin 3),
        Tendsto (fun n => mu.real
          (P.pairMergeErrorUnion (template (n + 1))
            ((template (n + 1)).image (P.shift
              (preferenceKingOffset (q (n + 1)).2 +
                if (q (n + 1)).1.val = 0 then 0
                else verticalShift (height n))))
            (radius (n + 1)))) atTop (nhds 0)) /\
      Tendsto (fun n => muDual.real (Edual.verticalCrossingEvent
        (4 * B) (4 * B + width n) (-4 * B)
          (targetY n (radius n) + 4 * B))) atTop (nhds 1) /\
      Tendsto (fun n => muDual.real (Edual.horizontalCrossingEvent
        (-4 * B) (width n + 12 * B) (4 * B)
          (4 * B + height n))) atTop (nhds 1) /\
      (forall n, (0 : Real) + 5 * B < width n + 8 * B - 5 * B) /\
      (forall n, -(4 * B : Real) + 5 * B <
        targetY n (radius n) + 4 * B - 5 * B) /\
      (forall n, -(4 * B : Real) + 5 * B <
        width n + 12 * B - 5 * B) /\
      (forall n, (0 : Real) + 5 * B <
        targetY n (radius n) + height n - 5 * B) /\
      (forall n : Nat, (0 : Real) + 4 * B <= 4 * B) /\
      (forall n, (4 * B : Real) + width n <=
        width n + 8 * B - 4 * B) /\
      (forall n : Nat, (0 : Real) + 4 * B <= 4 * B) /\
      (forall n, (4 * B : Real) + height n <=
        targetY n (radius n) + height n - 4 * B) := by
  let r : Nat -> Int -> Nat -> Real := fun _ _ _ => 4 * B
  let y : Nat -> Int -> Nat -> Real := fun _ _ _ => 4 * B
  let s : Nat -> Int -> Nat -> Real := fun n _ radius =>
    -(targetY n radius : Real) - 12 * B
  let t : Nat -> Int -> Nat -> Int := fun n _ radius =>
    (3 * targetY n radius + 24 * B : Nat)
  let minimumWidth' : Nat -> Int -> Nat -> Nat := fun n _ radius =>
    minimumWidth n radius
  let minimumHeight : Nat -> Int -> Nat -> Nat := fun _ _ _ => 0
  let horizontalLeft : Nat -> Int -> Nat -> Nat -> Int := fun _ _ _ _ =>
    -(4 * (B : Int))
  let horizontalRight : Nat -> Int -> Nat -> Nat -> Int := fun _ _ _ w =>
    w + 12 * (B : Int)
  have ht (n : Nat) (step : Int) (radius : Nat) :
      3 * (B : Real) < t n step radius := by
    dsimp only [t]
    push_cast
    have hBreal : (0 : Real) < B := by exact_mod_cast hBpos
    have hy : (20 * B + 1 : Real) <= targetY n radius := by
      exact_mod_cast htargetY n radius
    nlinarith
  have hhorizontalSpan (n : Nat) (step : Int) (radius width : Nat)
      (_hwidth : minimumWidth' n step radius <= width) :
      3 * (B : Real) <
        horizontalRight n step radius width -
          horizontalLeft n step radius width := by
    dsimp only [horizontalRight, horizontalLeft]
    push_cast
    have hBreal : (0 : Real) < B := by exact_mod_cast hBpos
    have hw : (0 : Real) <= width := by positivity
    nlinarith
  obtain ⟨state, rows, _hstate0, hstateSucc, _hstepNonneg,
      hradius, _hmerge, hmergeShift, hvertical, hhorizontal⟩ :=
    exists_recursiveDependentRadiusFirstAdjacentEndpointRows_with_limits
      E Edual mu muDual hunique hFKGDual hTIDual huniqueDual
      (B : Real) (by positivity) hB template 0 (by omega)
      r y s t ht minimumWidth' minimumHeight horizontalLeft horizontalRight
        hhorizontalSpan
  let radius : Nat -> Nat := fun n => (rows n).radius
  let width : Nat -> Nat := fun n => (rows n).width
  let height : Nat -> Nat := fun n => (rows n).height
  have hstateStep (n : Nat) : (state (n + 1)).1 = (height n : Int) := by
    rw [hstateSucc n]
  have hmergeCarried (q : Nat -> Fin 2 × (Fin 3 × Fin 3)) :
      Tendsto (fun n => mu.real
        (P.pairMergeErrorUnion (template (n + 1))
          ((template (n + 1)).image (P.shift
            (preferenceKingOffset (q (n + 1)).2 +
              if (q (n + 1)).1.val = 0 then 0
              else verticalShift (height n))))
          (radius (n + 1)))) atTop (nhds 0) := by
    apply (hmergeShift q).congr'
    filter_upwards [] with n
    simp only [hstateStep n, radius]
  have hvertical' : Tendsto (fun n => muDual.real
      (Edual.verticalCrossingEvent (4 * B) (4 * B + width n)
        (-4 * B) (targetY n (radius n) + 4 * B))) atTop (nhds 1) := by
    apply hvertical.congr'
    filter_upwards [] with n
    congr 2 <;> dsimp only [r, s, t, width] <;> push_cast <;> ring
  have hhorizontal' : Tendsto (fun n => muDual.real
      (Edual.horizontalCrossingEvent (-4 * B) (width n + 12 * B)
        (4 * B) (4 * B + height n))) atTop (nhds 1) := by
    apply hhorizontal.congr'
    filter_upwards [] with n
    congr 2 <;>
      dsimp only [horizontalLeft, horizontalRight, y, width, height] <;>
      push_cast <;> ring
  have hwidthLower (n : Nat) : minimumWidth n (radius n) <= width n :=
    (rows n).minimumWidth_le
  refine ⟨radius, width, height, hradius, hwidthLower, hmergeCarried,
    hvertical', hhorizontal', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    have hw0 : 3 * B + 1 <= width n :=
      (hminimumWidth n (radius n)).trans (hwidthLower n)
    have hw : (3 * B + 1 : Real) <= width n := by exact_mod_cast hw0
    have hBreal : (0 : Real) < B := by exact_mod_cast hBpos
    norm_num at hw ⊢
    linarith
  · intro n
    have hy : (20 * B + 1 : Real) <= targetY n (radius n) := by
      exact_mod_cast htargetY n (radius n)
    have hBreal : (0 : Real) < B := by exact_mod_cast hBpos
    push_cast
    nlinarith
  · intro n
    have hBreal : (0 : Real) < B := by exact_mod_cast hBpos
    have hw : (0 : Real) <= width n := by positivity
    push_cast
    linarith
  · intro n
    have hy : (20 * B + 1 : Real) <= targetY n (radius n) := by
      exact_mod_cast htargetY n (radius n)
    have hBreal : (0 : Real) < B := by exact_mod_cast hBpos
    have hh : (0 : Real) <= height n := by positivity
    push_cast
    nlinarith
  · intro n
    norm_num
  · intro n
    have hBreal : (0 : Real) <= B := by positivity
    push_cast
    linarith
  · intro n
    norm_num
  · intro n
    have hy : (20 * B + 1 : Real) <= targetY n (radius n) := by
      exact_mod_cast htargetY n (radius n)
    push_cast
    linarith


theorem exists_carriedAsymmetricEndpointCoordinates_with_requirements
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (B : Nat) (hBpos : 0 < B)
    (hB : forall {x z : W} (hxz : Pdual.graph.Adj x z)
      (u) (i : Fin 2),
      |Edual.coordinates (Edual.edgeArc hxz u - Edual.vertex x) i| <= B)
    (template : Nat -> Finset V)
    (minimumWidth targetY : Nat -> Nat)
    (hminimumWidth : forall n, 3 * B + 1 <= minimumWidth n)
    (htargetY : forall n, 20 * B + 1 <= targetY n) :
    exists radius width height : Nat -> Nat,
      Tendsto radius atTop atTop /\
      (forall n, minimumWidth n <= width n) /\
      (forall q : Nat -> Fin 2 × (Fin 3 × Fin 3),
        Tendsto (fun n => mu.real
          (P.pairMergeErrorUnion (template (n + 1))
            ((template (n + 1)).image (P.shift
              (preferenceKingOffset (q (n + 1)).2 +
                if (q (n + 1)).1.val = 0 then 0
                else verticalShift (height n))))
            (radius (n + 1)))) atTop (nhds 0)) /\
      Tendsto (fun n => muDual.real (Edual.verticalCrossingEvent
        (4 * B) (4 * B + width n) (-4 * B)
          (targetY n + 4 * B))) atTop (nhds 1) /\
      Tendsto (fun n => muDual.real (Edual.horizontalCrossingEvent
        (-4 * B) (width n + 12 * B) (4 * B)
          (4 * B + height n))) atTop (nhds 1) /\
      (forall n, (0 : Real) + 5 * B < width n + 8 * B - 5 * B) /\
      (forall n, -(4 * B : Real) + 5 * B <
        targetY n + 4 * B - 5 * B) /\
      (forall n, -(4 * B : Real) + 5 * B <
        width n + 12 * B - 5 * B) /\
      (forall n, (0 : Real) + 5 * B <
        targetY n + height n - 5 * B) /\
      (forall n : Nat, (0 : Real) + 4 * B <= 4 * B) /\
      (forall n, (4 * B : Real) + width n <=
        width n + 8 * B - 4 * B) /\
      (forall n : Nat, (0 : Real) + 4 * B <= 4 * B) /\
      (forall n, (4 * B : Real) + height n <=
        targetY n + height n - 4 * B) := by
  simpa using
    (exists_carriedAsymmetricEndpointCoordinates_with_radius_requirements
      E Edual mu muDual hunique hFKGDual hTIDual huniqueDual B hBpos hB
      template (fun n _ => minimumWidth n) (fun n _ => targetY n)
      (fun n _ => hminimumWidth n) (fun n _ => htargetY n))


theorem PeriodicPlanarDualPair.exists_carriedAsymmetricEndpoints_false_of_primal_limit_with_requirements
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG (D.dualMeasure mu))
    (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu))
    (huniqueDual : (D.dualMeasure mu)
      {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (B : Nat) (hBpos : 0 < B)
    (hBp : forall {x z : V} (hxz : P.graph.Adj x z)
      (u) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxz u - D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x z : W} (hxz : Pdual.graph.Adj x z)
      (u) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxz u - D.dualEmbedding.vertex x) i| <= B)
    (template : Nat -> Finset V)
    (minimumWidth targetY : Nat -> Nat)
    (hminimumWidth : forall n, 3 * B + 1 <= minimumWidth n)
    (htargetY : forall n, 20 * B + 1 <= targetY n) :
    exists radius width height : Nat -> Nat,
      Tendsto radius atTop atTop /\
      (forall n, minimumWidth n <= width n) /\
      (forall q : Nat -> Fin 2 × (Fin 3 × Fin 3),
        Tendsto (fun n => mu.real
          (P.pairMergeErrorUnion (template (n + 1))
            ((template (n + 1)).image (P.shift
              (preferenceKingOffset (q (n + 1)).2 +
                if (q (n + 1)).1.val = 0 then 0
                else verticalShift (height n))))
            (radius (n + 1)))) atTop (nhds 0)) /\
      (Tendsto (fun n => max
        (mu.real (D.primalEmbedding.horizontalCrossingEvent
          0 (width n + 8 * B) 0 (targetY n)))
        (mu.real (D.primalEmbedding.verticalCrossingEvent
          0 (width n + 8 * B) 0 (targetY n + height n))))
        atTop (nhds 1) -> False) := by
  letI : IsProbabilityMeasure (D.dualMeasure mu) :=
    inferInstance
  obtain ⟨radius, width, height, hradius, hwidth, hmerge,
      hdualV0, hdualH0, hspanHX, hspanDVY, hspanDHX, hspanVY,
      hDVLeft, hDVRight, hDHBottom, hDHTop⟩ :=
    exists_carriedAsymmetricEndpointCoordinates_with_requirements
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu)
      hunique hFKGDual hTIDual huniqueDual B hBpos hBd template
      minimumWidth targetY hminimumWidth htargetY
  have hdualV : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (4 * B) (4 * B + width n) (-4 * B)
          (targetY n + 4 * B))) atTop (nhds 1) := by
    apply hdualV0.congr'
    filter_upwards [] with n
    rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.verticalCrossingEvent_measurableSet _ _ _ _)]
  have hdualH : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (-4 * B) (width n + 12 * B) (4 * B)
          (4 * B + height n))) atTop (nhds 1) := by
    apply hdualH0.congr'
    filter_upwards [] with n
    rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.horizontalCrossingEvent_measurableSet _ _ _ _)]
  have hspanDVY' : forall n,
      -(4 * B : Real) + 5 * B <
        (targetY n : Real) + 4 * B - 5 * B := by
    simpa using hspanDVY
  have hspanVY' : forall n,
      (0 : Real) + 5 * B <
        (targetY n : Real) + height n - 5 * B := by
    simpa using hspanVY
  have hDHTop' : forall n,
      (4 * B : Real) + height n <=
        (targetY n : Real) + height n - 4 * B := by
    simpa using hDHTop
  refine ⟨radius, width, height, hradius, hwidth, hmerge, ?_⟩
  intro hprimal
  exact D.fullyAsymmetricEndpointCoordinates_false mu (B : Real)
    (by exact_mod_cast hBpos) hBp hBd
    (fun _ => 0) (fun n => width n + 8 * B)
    (fun _ => 0) (fun n => (targetY n : Real))
    (fun _ => 0) (fun n => width n + 8 * B)
    (fun _ => 0) (fun n => (targetY n : Real) + height n)
    (fun _ => 4 * B) (fun n => 4 * B + width n)
    (fun _ => -4 * B) (fun n => targetY n + 4 * B)
    (fun _ => -4 * B) (fun n => width n + 12 * B)
    (fun _ => 4 * B) (fun n => 4 * B + height n)
    hspanHX (fun n => by nlinarith [hspanDVY' n])
    (fun n => by nlinarith [hspanDHX n]) hspanVY'
    (fun _ => by norm_num) (fun _ => by norm_num)
    hDVLeft hDVRight
    (fun _ => by norm_num) (fun _ => by apply le_of_eq; ring)
    hDHBottom hDHTop' hprimal hdualV hdualH


theorem PeriodicPlaneEmbedding.centeredCrossingMax_tendsto_origin
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (M outerWidth outerHeight step : Nat -> Nat)
    (hwidth : forall n, 2 * M n <= outerWidth n)
    (hheight : forall n, 2 * M n <= outerHeight n)
    (hcentered : Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        (-(M n : Real))
        (M n + (outerWidth n - 2 * M n) : Nat)
        (-(M n : Real))
        (M n + (outerHeight n - 2 * M n) : Nat)))
      (mu.real (E.verticalCrossingEvent
        (-(M n : Real))
        (M n + (outerWidth n - 2 * M n) : Nat)
        (-(M n : Real))
        ((M n + (outerHeight n - 2 * M n) : Nat) + step n))))
      atTop (nhds 1)) :
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        0 (outerWidth n) 0 (outerHeight n)))
      (mu.real (E.verticalCrossingEvent
        0 (outerWidth n) 0 (outerHeight n + step n))))
      atTop (nhds 1) := by
  let z : Nat -> Site 2 := fun n => ![(M n : Int), (M n : Int)]
  have htranslated := E.crossingMax_independent_translate_tendsto_one
    mu hTI z z
    (fun n => -(M n : Real))
    (fun n => (M n + (outerWidth n - 2 * M n) : Nat))
    (fun n => -(M n : Real))
    (fun n => (M n + (outerHeight n - 2 * M n) : Nat))
    (fun n => -(M n : Real))
    (fun n => (M n + (outerWidth n - 2 * M n) : Nat))
    (fun n => -(M n : Real))
    (fun n => ((M n + (outerHeight n - 2 * M n) : Nat) + step n))
    hcentered
  apply htranslated.congr'
  filter_upwards [] with n
  have hwn := hwidth n
  have hhn := hheight n
  congr 3 <;> simp [z]
  all_goals first | rw [Nat.cast_sub hwn] | rw [Nat.cast_sub hhn]
  all_goals push_cast <;> ring


theorem PeriodicPlaneEmbedding.adjacentCrossingMax_tendsto_one_mono_vertical_width
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (a b c d step aVertical bVertical : Nat -> Real)
    (ha : forall n, aVertical n <= a n)
    (hb : forall n, b n <= bVertical n)
    (hlimit : Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        (a n) (b n) (c n) (d n)))
      (mu.real (E.verticalCrossingEvent
        (a n) (b n) (c n) (d n + step n)))) atTop (nhds 1)) :
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        (a n) (b n) (c n) (d n)))
      (mu.real (E.verticalCrossingEvent
        (aVertical n) (bVertical n) (c n) (d n + step n))))
      atTop (nhds 1) := by
  exact hlimit.squeeze tendsto_const_nhds
    (fun n => max_le_max (le_refl _)
      (measureReal_mono
        (E.verticalCrossingEvent_mono_horizontal (ha n) (hb n))))
    (fun _ => max_le measureReal_le_one measureReal_le_one)


theorem PeriodicPlanarDualPair.pointwiseRecursiveRectangleArray_false_of_primal_dualMeasure_limits
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
    (a b c d : Nat -> Nat -> Real)
    (hspanX : forall k n, a k n + 5 * B < b k n - 5 * B)
    (hspanY : forall k n, c k n + 5 * B < d k n - 5 * B)
    (hverticalStart : Tendsto (fun n => mu.real
      (D.primalEmbedding.verticalCrossingEvent
        (a 0 n + 4 * B) (b 0 n - 4 * B) (c 0 n) (d 0 n)))
      atTop (nhds 1))
    (hhorizontalLevel : forall k, Tendsto (fun n => mu.real
      (D.primalEmbedding.horizontalCrossingEvent
        (a (k + 1) n) (b (k + 1) n)
        (c (k + 1) n + 4 * B) (d (k + 1) n - 4 * B)))
      atTop (nhds 1))
    (hnormalAdjacent : forall k, Tendsto (fun n => max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent
        (a k n) (b k n) (c k n + 4 * B) (d k n - 4 * B)))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (a (k + 1) n + 4 * B) (b (k + 1) n - 4 * B)
        (c (k + 1) n) (d (k + 1) n)))) atTop (nhds 1))
    (hdualLevel : forall k, Tendsto (fun n => max
      ((D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent
        (a k n + 4 * B) (b k n - 4 * B) (c k n) (d k n)))
      ((D.dualMeasure mu).real (D.dualEmbedding.horizontalCrossingEvent
        (a k n) (b k n) (c k n + 4 * B) (d k n - 4 * B))))
      atTop (nhds 1)) : False := by
  apply D.pointwiseRecursiveRectangleArray_false_of_normal_rotated_limits
    mu B hBpos hBp hBd a b c d hspanX hspanY hverticalStart
    hhorizontalLevel hnormalAdjacent
  intro k
  exact D.dualMeasure_crossingMax_tendsto_one mu
    (fun n => a k n + 4 * B) (fun n => b k n - 4 * B)
    (c k) (d k) (a k) (b k)
    (fun n => c k n + 4 * B) (fun n => d k n - 4 * B)
    (hdualLevel k)


end StatMech.FK.PeriodicPlanar
