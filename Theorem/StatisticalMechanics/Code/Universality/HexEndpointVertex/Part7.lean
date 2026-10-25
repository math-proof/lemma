/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointWalk.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexCyclicVertexPartition.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Def.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part7


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

@[simp] theorem anchoredLoopReverse_nil : anchoredLoopReverse [] = [] := rfl

@[simp] theorem anchoredLoopReverse_cons (t : ℤ) (ts : List ℤ) :
    anchoredLoopReverse (t :: ts) = (-t) :: loopReverse ts := rfl

theorem anchoredLoopReverse_sum (L : List ℤ) :
    (anchoredLoopReverse L).sum = -L.sum := by
  cases L with
  | nil => simp
  | cons t ts =>
      simp only [anchoredLoopReverse_cons, List.sum_cons, loopReverse_sum]
      ring

@[simp] theorem anchoredLoopReverse_length (L : List ℤ) :
    (anchoredLoopReverse L).length = L.length := by
  cases L <;> simp [anchoredLoopReverse, loopReverse_length]

theorem anchoredLoopReverse_legal (L : List ℤ)
    (hL : ∀ t ∈ L, t = 1 ∨ t = -1) :
    ∀ t ∈ anchoredLoopReverse L, t = 1 ∨ t = -1 := by
  cases L with
  | nil => simp
  | cons u us =>
      have hu := hL u (by simp)
      have hus : ∀ t ∈ us, t = 1 ∨ t = -1 := by
        intro t ht
        exact hL t (by simp [ht])
      have hrev := loopReverse_legal us hus
      intro t ht
      simp only [anchoredLoopReverse_cons, List.mem_cons] at ht
      rcases ht with rfl | ht
      · rcases hu with rfl | rfl <;> simp
      · exact hrev t ht

@[simp] theorem anchoredLoopReverse_involutive (L : List ℤ) :
    anchoredLoopReverse (anchoredLoopReverse L) = L := by
  cases L with
  | nil => rfl
  | cons t ts =>
      simp [anchoredLoopReverse, loopReverse_involutive]


theorem hexEndpoint_midsAux_loopReverse_exact
    (m : ℂ) (h : ℤ) (L : List ℤ)
    (hlegal : ∀ t ∈ L, t = 1 ∨ t = -1) :
    midsAux (hexInfra_midAccum m h L)
        (hexInfra_headAccum h L + 3) (loopReverse L) =
      (midsAux m h L).reverse := by
  induction L using List.reverseRecOn generalizing m h with
  | nil => simp [loopReverse]
  | append_singleton xs t ih =>
      have ht : t = 1 ∨ t = -1 := hlegal t (by simp)
      have hxs : ∀ u ∈ xs, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      let p := hexInfra_midAccum m h xs
      let k := hexInfra_headAccum h xs
      have hmid : hexInfra_midAccum m h (xs ++ [t]) =
          p + halfStep k + halfStep (k + t) := by
        rw [hexCyclic_midAccum_append_single]
      have hhead : hexInfra_headAccum h (xs ++ [t]) = k + t := by
        simp [hexInfra_headAccum_eq_add_sum, List.sum_append, k]
        ring
      have hrev : loopReverse (xs ++ [t]) = (-t) :: loopReverse xs := by
        simp [loopReverse]
      have hstep1 : halfStep (k + t + 3) = -halfStep (k + t) := by
        simpa only [add_assoc] using hexEndpoint_halfStep_add_three (k + t)
      have hstep2 : halfStep (k + t + 3 + -t) = -halfStep k := by
        rw [show k + t + 3 + -t = k + 3 by ring,
          hexEndpoint_halfStep_add_three]
      rw [hmid, hhead, hrev, midsAux_cons, hstep1, hstep2]
      have hreturn : p + halfStep k + halfStep (k + t) +
          -halfStep (k + t) + -halfStep k = p := by ring
      rw [hreturn]
      have hheading : k + t + 3 + -t = k + 3 := by ring
      rw [hheading, ih m h hxs]
      rw [hexCyclic_midsAux_append_single, List.reverse_append]
      simp [p, k]


theorem hexEndpoint_verticesAux_loopReverse_exact
    (m : ℂ) (h : ℤ) (L : List ℤ)
    (hlegal : ∀ t ∈ L, t = 1 ∨ t = -1) :
    verticesAux (hexInfra_midAccum m h L)
        (hexInfra_headAccum h L + 3) (loopReverse L) =
      (verticesAux m h L).dropLast.reverse ++ [m - halfStep h] := by
  induction L using List.reverseRecOn generalizing m h with
  | nil =>
      simp only [hexInfra_midAccum_nil, hexInfra_headAccum_nil,
        loopReverse, List.map_nil, List.reverse_nil, verticesAux_nil,
        List.dropLast_singleton, List.reverse_nil, List.nil_append]
      rw [hexEndpoint_halfStep_add_three]
      ring
  | append_singleton xs t ih =>
      have ht : t = 1 ∨ t = -1 := hlegal t (by simp)
      have hxs : ∀ u ∈ xs, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      let p := hexInfra_midAccum m h xs
      let k := hexInfra_headAccum h xs
      have hmid : hexInfra_midAccum m h (xs ++ [t]) =
          p + halfStep k + halfStep (k + t) := by
        rw [hexCyclic_midAccum_append_single]
      have hhead : hexInfra_headAccum h (xs ++ [t]) = k + t := by
        simp [hexInfra_headAccum_eq_add_sum, List.sum_append, k]
        ring
      have hrev : loopReverse (xs ++ [t]) = (-t) :: loopReverse xs := by
        simp [loopReverse]
      have hstep1 : halfStep (k + t + 3) = -halfStep (k + t) := by
        simpa only [add_assoc] using hexEndpoint_halfStep_add_three (k + t)
      have hstep2 : halfStep (k + t + 3 + -t) = -halfStep k := by
        rw [show k + t + 3 + -t = k + 3 by ring,
          hexEndpoint_halfStep_add_three]
      rw [hmid, hhead, hrev, verticesAux_cons, hstep1, hstep2]
      have hfirst : p + halfStep k + halfStep (k + t) +
          -halfStep (k + t) = p + halfStep k := by ring
      rw [hfirst]
      have hreturn : p + halfStep k + -halfStep k = p := by ring
      rw [hreturn]
      have hheading : k + t + 3 + -t = k + 3 := by ring
      rw [hheading, ih m h hxs]
      rw [endpointVerticesAux_append_one]
      rw [show verticesAux m h xs =
          (verticesAux m h xs).dropLast ++
            [p + halfStep k] by
        have hn : verticesAux m h xs ≠ [] :=
          hexInfra_verticesAux_ne_nil m h xs
        have hlast : (verticesAux m h xs).getLast hn = p + halfStep k := by
          have hg := hexInfra_verticesAux_getLast? m h xs
          rw [List.getLast?_eq_some_getLast hn] at hg
          exact Option.some.inj hg
        rw [← hlast]
        exact (List.dropLast_append_getLast hn).symm]
      simp [List.reverse_append]


theorem hexEndpoint_midsAux_append (m : ℂ) (h : ℤ)
    (xs ys : List ℤ) :
    midsAux m h (xs ++ ys) =
      (midsAux m h xs).dropLast ++
        midsAux (hexInfra_midAccum m h xs)
          (hexInfra_headAccum h xs) ys := by
  induction xs generalizing m h with
  | nil => simp
  | cons t ts ih =>
      simp only [List.cons_append, midsAux_cons,
        hexInfra_midAccum_cons, hexInfra_headAccum_cons]
      rw [List.dropLast_cons_of_ne_nil]
      · rw [ih]
        rfl
      · cases ts <;> simp [midsAux]


theorem hexEndpoint_verticesAux_append (m : ℂ) (h : ℤ)
    (xs ys : List ℤ) :
    verticesAux m h (xs ++ ys) =
      (verticesAux m h xs).dropLast ++
        verticesAux (hexInfra_midAccum m h xs)
          (hexInfra_headAccum h xs) ys := by
  induction xs generalizing m h with
  | nil => simp
  | cons t ts ih =>
      simp only [List.cons_append, verticesAux_cons,
        hexInfra_midAccum_cons, hexInfra_headAccum_cons]
      rw [List.dropLast_cons_of_ne_nil]
      · rw [ih]
        rfl
      · exact hexInfra_verticesAux_ne_nil _ _ _


theorem hexEndpoint_dropLast_verticesAux_append (m : ℂ) (h : ℤ)
    (xs ys : List ℤ) :
    (verticesAux m h (xs ++ ys)).dropLast =
      (verticesAux m h xs).dropLast ++
        (verticesAux (hexInfra_midAccum m h xs)
          (hexInfra_headAccum h xs) ys).dropLast := by
  rw [hexEndpoint_verticesAux_append]
  rw [List.dropLast_append_of_ne_nil
    (hexInfra_verticesAux_ne_nil _ _ _)]


theorem anchoredLoopReverse_midsAux_eq
    (m : ℂ) (h : ℤ) (tail : List ℤ)
    (hlegal : ∀ t ∈ (1 : ℤ) :: tail, t = 1 ∨ t = -1)
    (hsum : ((1 : ℤ) :: tail).sum = -4)
    (hclose : hexInfra_midAccum m h ((1 : ℤ) :: tail) +
      halfStep (hexInfra_headAccum h ((1 : ℤ) :: tail)) =
        m + halfStep h) :
    midsAux m h (anchoredLoopReverse ((1 : ℤ) :: tail)) =
      m :: (midsAux m h ((1 : ℤ) :: tail)).tail.reverse := by
  let m1 := m + halfStep h + halfStep (h + 1)
  let H := hexInfra_headAccum (h + 1) tail
  let M := hexInfra_midAccum m1 (h + 1) tail
  have htail : ∀ t ∈ tail, t = 1 ∨ t = -1 := by
    intro t ht
    exact hlegal t (by simp [ht])
  have hH : H = h - 4 := by
    dsimp [H]
    simp only [hexInfra_headAccum_eq_add_sum, List.sum_cons] at hsum ⊢
    omega
  have hclose' : M + halfStep H = m + halfStep h := by
    simpa only [hexInfra_midAccum_cons, hexInfra_headAccum_cons, M, H, m1]
      using hclose
  have hopp : halfStep (h - 1) = -halfStep H := by
    rw [hH, show h - 1 = h - 4 + 3 by ring,
      hexEndpoint_halfStep_add_three]
  have hfirst : m + halfStep h + halfStep (h - 1) = M := by
    rw [hopp]
    linear_combination -hclose'
  have hheading : h - 1 = H + 3 := by rw [hH]; ring
  rw [anchoredLoopReverse_cons, midsAux_cons]
  rw [show h + (-1 : ℤ) = h - 1 by ring, hfirst, hheading]
  rw [hexEndpoint_midsAux_loopReverse_exact m1 (h + 1) tail htail]
  simp only [midsAux_cons, List.tail_cons]
  rfl


theorem anchoredLoopReverse_midAccum_eq
    (m : ℂ) (h : ℤ) (tail : List ℤ)
    (hlegal : ∀ t ∈ (1 : ℤ) :: tail, t = 1 ∨ t = -1)
    (hsum : ((1 : ℤ) :: tail).sum = -4)
    (hclose : hexInfra_midAccum m h ((1 : ℤ) :: tail) +
      halfStep (hexInfra_headAccum h ((1 : ℤ) :: tail)) =
        m + halfStep h) :
    hexInfra_midAccum m h
        (anchoredLoopReverse ((1 : ℤ) :: tail)) =
      m + halfStep h + halfStep (h + 1) := by
  have htrace := anchoredLoopReverse_midsAux_eq
    m h tail hlegal hsum hclose
  have hlast := congrArg List.getLast? htrace
  rw [hexInfra_midsAux_getLast?] at hlast
  simp only [midsAux_cons, List.tail_cons] at hlast
  rw [List.getLast?_cons] at hlast
  have hhead :
      (midsAux (m + halfStep h + halfStep (h + 1))
        (h + 1) tail).head?.getD m =
          m + halfStep h + halfStep (h + 1) := by
    cases tail <;> rfl
  rw [List.getLast?_reverse, hhead] at hlast
  exact Option.some.inj hlast


theorem anchoredLoopReverse_verticesAux_eq
    (m : ℂ) (h : ℤ) (tail : List ℤ)
    (hlegal : ∀ t ∈ (1 : ℤ) :: tail, t = 1 ∨ t = -1)
    (hsum : ((1 : ℤ) :: tail).sum = -4)
    (hclose : hexInfra_midAccum m h ((1 : ℤ) :: tail) +
      halfStep (hexInfra_headAccum h ((1 : ℤ) :: tail)) =
        m + halfStep h) :
    verticesAux m h (anchoredLoopReverse ((1 : ℤ) :: tail)) =
      (m + halfStep h) ::
        (verticesAux m h ((1 : ℤ) :: tail)).dropLast.tail.reverse ++
          [m + halfStep h] := by
  let m1 := m + halfStep h + halfStep (h + 1)
  let H := hexInfra_headAccum (h + 1) tail
  let M := hexInfra_midAccum m1 (h + 1) tail
  have htail : ∀ t ∈ tail, t = 1 ∨ t = -1 := by
    intro t ht
    exact hlegal t (by simp [ht])
  have hH : H = h - 4 := by
    dsimp [H]
    simp only [hexInfra_headAccum_eq_add_sum, List.sum_cons] at hsum ⊢
    omega
  have hclose' : M + halfStep H = m + halfStep h := by
    simpa only [hexInfra_midAccum_cons, hexInfra_headAccum_cons, M, H, m1]
      using hclose
  have hopp : halfStep (h - 1) = -halfStep H := by
    rw [hH, show h - 1 = h - 4 + 3 by ring,
      hexEndpoint_halfStep_add_three]
  have hfirst : m + halfStep h + halfStep (h - 1) = M := by
    rw [hopp]
    linear_combination -hclose'
  have hheading : h - 1 = H + 3 := by rw [hH]; ring
  rw [anchoredLoopReverse_cons, verticesAux_cons]
  rw [show h + (-1 : ℤ) = h - 1 by ring, hfirst, hheading]
  rw [hexEndpoint_verticesAux_loopReverse_exact m1 (h + 1) tail htail]
  have hback : m1 - halfStep (h + 1) = m + halfStep h := by
    dsimp [m1]
    ring
  rw [hback]
  have hn : verticesAux m1 (h + 1) tail ≠ [] :=
    hexInfra_verticesAux_ne_nil m1 (h + 1) tail
  rw [verticesAux_cons, List.dropLast_cons_of_ne_nil hn, List.tail_cons]
  rfl


theorem anchoredLoopReverse_endpointVertices_eq
    (m : ℂ) (h : ℤ) (tail : List ℤ)
    (hlegal : ∀ t ∈ (1 : ℤ) :: tail, t = 1 ∨ t = -1)
    (hsum : ((1 : ℤ) :: tail).sum = -4)
    (hclose : hexInfra_midAccum m h ((1 : ℤ) :: tail) +
      halfStep (hexInfra_headAccum h ((1 : ℤ) :: tail)) =
        m + halfStep h) :
    (verticesAux m h
        (anchoredLoopReverse ((1 : ℤ) :: tail))).dropLast =
      (m + halfStep h) ::
        (verticesAux m h ((1 : ℤ) :: tail)).dropLast.tail.reverse := by
  rw [anchoredLoopReverse_verticesAux_eq m h tail hlegal hsum hclose]
  rw [List.dropLast_append_of_ne_nil
    (by simp : [m + halfStep h] ≠ []), List.dropLast_singleton,
    List.append_nil]


theorem endpoint_genuine_pair_zero_via_anchored_reversal
    (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (v du : ℂ)
    (base Lq : List ℤ) (hLqsum : Lq.sum = -4)
    (hq : (ofTurns a h0 (base ++ Lq)).EndpointIsLegalSAW ∧
      (ofTurns a h0 (base ++ Lq)).StaysIn region ∧
      (ofTurns a h0 (base ++ Lq)).EndsAt (v + hexOmega * du))
    (hr : (ofTurns a h0 (base ++ anchoredLoopReverse Lq)).EndpointIsLegalSAW ∧
      (ofTurns a h0 (base ++ anchoredLoopReverse Lq)).StaysIn region ∧
      (ofTurns a h0 (base ++ anchoredLoopReverse Lq)).EndsAt
        (v + hexOmega ^ 2 * du)) :
    ((v + hexOmega * du) - v) *
        endpointParafSummand region a h0 (v + hexOmega * du)
          (5 / 8) hexChi (base ++ Lq) +
      ((v + hexOmega ^ 2 * du) - v) *
        endpointParafSummand region a h0 (v + hexOmega ^ 2 * du)
          (5 / 8) hexChi (base ++ anchoredLoopReverse Lq) = 0 :=
  endpoint_genuine_pair_zero region a h0 v du base Lq
    (anchoredLoopReverse Lq) hLqsum
    (by rw [anchoredLoopReverse_sum, hLqsum]; ring)
    (anchoredLoopReverse_length Lq).symm hq hr


end
end StatMech.Universality
