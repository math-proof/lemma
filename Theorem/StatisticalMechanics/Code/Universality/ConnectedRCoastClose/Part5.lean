/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.BoxCrossing.Part3
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.BXPAllAspect
import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.PlanarMengerDualityClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.MengerBarrierClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.CoastlineContinuityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.CoastlineAnchorClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.CircuitReachClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.BoxArcConnectsClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.RCoastMengerClose.Part2
import Def.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part4
open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped NNReal
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem crr_leftReach_openWalk_lift (omega : ConfigSpace (Sym2 (Site 2))) (n : Int)
    {u v : rect 0 n 0 n} (hu : (u : Site 2) ∈ bcd_leftReach omega n)
    (w : (openSubgraphInduce 2 omega (rect 0 n 0 n)).Walk u v) :
    ∃ hv : (v : Site 2) ∈ bcd_leftReach omega n,
      ((hypercubicLattice 2).induce (bcd_leftReach omega n)).Reachable
        ⟨u, hu⟩ ⟨v, hv⟩ := by
  induction w with
  | nil => exact ⟨hu, SimpleGraph.Reachable.refl _⟩
  | @cons a b c hab p ih =>
      have habOpen : (openSubgraph 2 omega).Adj (a : Site 2) (b : Site 2) := hab
      have hb : (b : Site 2) ∈ bcd_leftReach omega n :=
        bcd_leftReach_extend omega n hu b.2 (openSubgraph_le omega habOpen) habOpen.2
      obtain ⟨hc, hbc⟩ := ih hb
      have habL : ((hypercubicLattice 2).induce (bcd_leftReach omega n)).Adj
          ⟨a, hu⟩ ⟨b, hb⟩ := by
        exact openSubgraph_le omega habOpen
      exact ⟨hc, habL.reachable.trans hbc⟩


theorem crr_leftWall_reaches_zero (omega : ConfigSpace (Sym2 (Site 2))) (n r : Int)
    (hr0 : 0 ≤ r) (hrn : r ≤ n) :
    ∃ (hr : (![0, r] : Site 2) ∈ bcd_leftReach omega n)
      (h0 : (![0, 0] : Site 2) ∈ bcd_leftReach omega n),
      ((hypercubicLattice 2).induce (bcd_leftReach omega n)).Reachable
        ⟨![0, r], hr⟩ ⟨![0, 0], h0⟩ := by
  have hn : 0 ≤ n := hr0.trans hrn
  have hmem : ∀ t : Int, 0 ≤ t → t ≤ n →
      (![0, t] : Site 2) ∈ bcd_leftReach omega n := by
    intro t ht0 htn
    apply jex_leftSide_subset_leftReach omega n
    refine ⟨?_, by simp⟩
    rw [mem_rect]
    exact ⟨by simp [hn], by simp [hn], by simpa using ht0, by simpa using htn⟩
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hr0
  have hseg : ∀ k : Nat, k ≤ m →
      Function.update (![0, 0] : Site 2) 1 ((![0, 0] : Site 2) 1 + (k : Int))
        ∈ bcd_leftReach omega n := by
    intro k hk
    have hval : Function.update (![0, 0] : Site 2) 1
        ((![0, 0] : Site 2) 1 + (k : Int)) = ![0, (k : Int)] := by
      funext i
      fin_cases i <;> simp [Function.update]
    rw [hval]
    have hk' : (k : Int) ≤ (m : Int) := by exact_mod_cast hk
    exact hmem (k : Int) (by positivity) (by omega)
  have hreach := segment_connectedWithin (d := 2) (bcd_leftReach omega n) (1 : Fin 2)
    (![0, 0] : Site 2) m hseg
  have e0 : Function.update (![0, 0] : Site 2) 1
      ((![0, 0] : Site 2) 1 + ((0 : Nat) : Int)) = ![0, 0] := by
    funext i
    fin_cases i <;> simp [Function.update]
  have em : Function.update (![0, 0] : Site 2) 1
      ((![0, 0] : Site 2) 1 + (m : Int)) = ![0, r] := by
    funext i
    fin_cases i
    · simp [Function.update]
    · simp only [Function.update]
      simp
      omega
  have h0 := hmem 0 le_rfl hn
  have hr := hmem r hr0 hrn
  have hsub0 : (⟨![0, 0], h0⟩ : bcd_leftReach omega n) =
      ⟨Function.update (![0, 0] : Site 2) 1
        ((![0, 0] : Site 2) 1 + ((0 : Nat) : Int)), hseg 0 (Nat.zero_le m)⟩ :=
    Subtype.ext e0.symm
  have hsubm : (⟨![0, r], hr⟩ : bcd_leftReach omega n) =
      ⟨Function.update (![0, 0] : Site 2) 1
        ((![0, 0] : Site 2) 1 + (m : Int)), hseg m le_rfl⟩ :=
    Subtype.ext em.symm
  refine ⟨hr, h0, ?_⟩
  rw [hsub0, hsubm]
  exact hreach.symm


theorem crr_leftReach_connected_pair (omega : ConfigSpace (Sym2 (Site 2))) (n : Int)
    {u v : Site 2} (hu : u ∈ bcd_leftReach omega n) (hv : v ∈ bcd_leftReach omega n) :
    ((hypercubicLattice 2).induce (bcd_leftReach omega n)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
  obtain ⟨_hubox, xu, hxu, hubox, hxuReach⟩ := hu
  obtain ⟨_hvbox, xv, hxv, hvbox, hxvReach⟩ := hv
  have hxueq : xu = ![0, xu 1] := by
    funext i
    fin_cases i
    · simpa using hxu.2
    · simp
  have hxveq : xv = ![0, xv 1] := by
    funext i
    fin_cases i
    · simpa using hxv.2
    · simp
  have hxub := mem_rect.mp hxu.1
  have hxvb := mem_rect.mp hxv.1
  obtain ⟨hxuL, hxu0, hxuTo0⟩ :=
    crr_leftWall_reaches_zero omega n (xu 1) hxub.2.2.1 hxub.2.2.2
  obtain ⟨hxvL, hxv0, hxvTo0⟩ :=
    crr_leftWall_reaches_zero omega n (xv 1) hxvb.2.2.1 hxvb.2.2.2
  have hxuL' : xu ∈ bcd_leftReach omega n := by rw [hxueq]; exact hxuL
  have hxvL' : xv ∈ bcd_leftReach omega n := by rw [hxveq]; exact hxvL
  have hxuSub : (⟨xu, hxuL'⟩ : bcd_leftReach omega n) = ⟨![0, xu 1], hxuL⟩ :=
    Subtype.ext hxueq
  have hxvSub : (⟨xv, hxvL'⟩ : bcd_leftReach omega n) = ⟨![0, xv 1], hxvL⟩ :=
    Subtype.ext hxveq
  have hxuTo0' : ((hypercubicLattice 2).induce (bcd_leftReach omega n)).Reachable
      ⟨xu, hxuL'⟩ ⟨![0, 0], hxu0⟩ := by rw [hxuSub]; exact hxuTo0
  have hxvTo0' : ((hypercubicLattice 2).induce (bcd_leftReach omega n)).Reachable
      ⟨xv, hxvL'⟩ ⟨![0, 0], hxv0⟩ := by rw [hxvSub]; exact hxvTo0
  obtain ⟨hu', hxuToU⟩ := crr_leftReach_openWalk_lift omega n hxuL' hxuReach.some
  obtain ⟨hv', hxvToV⟩ := crr_leftReach_openWalk_lift omega n hxvL' hxvReach.some
  have hzero : (⟨![0, 0], hxu0⟩ : bcd_leftReach omega n) = ⟨![0, 0], hxv0⟩ := rfl
  rw [hzero] at hxuTo0'
  have hmid := hxuToU.symm.trans (hxuTo0'.trans (hxvTo0'.symm.trans hxvToV))
  exact hmid


theorem crr_leftWall_reaches_boxVertex (n : Int) {u : Site 2}
    (hu : u ∈ rect 0 n 0 n) :
    ∃ hl : (![0, u 1] : Site 2) ∈ rect 0 n 0 n,
      ((hypercubicLattice 2).induce (rect 0 n 0 n)).Reachable
        ⟨![0, u 1], hl⟩ ⟨u, hu⟩ := by
  have hub := mem_rect.mp hu
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hub.1
  have hseg : ∀ k : Nat, k ≤ m →
      Function.update (![0, u 1] : Site 2) 0
        ((![0, u 1] : Site 2) 0 + (k : Int)) ∈ rect 0 n 0 n := by
    intro k hk
    have hval : Function.update (![0, u 1] : Site 2) 0
        ((![0, u 1] : Site 2) 0 + (k : Int)) = ![(k : Int), u 1] := by
      funext i
      fin_cases i <;> simp [Function.update]
    rw [hval, mem_rect]
    have hk' : (k : Int) ≤ (m : Int) := by exact_mod_cast hk
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have hreach := segment_connectedWithin (d := 2) (rect 0 n 0 n) (0 : Fin 2)
    (![0, u 1] : Site 2) m hseg
  have e0 : Function.update (![0, u 1] : Site 2) 0
      ((![0, u 1] : Site 2) 0 + ((0 : Nat) : Int)) = ![0, u 1] := by
    funext i
    fin_cases i <;> simp [Function.update]
  have em : Function.update (![0, u 1] : Site 2) 0
      ((![0, u 1] : Site 2) 0 + (m : Int)) = u := by
    funext i
    fin_cases i
    · simp only [Function.update]
      simp
      omega
    · simp [Function.update]
  have hl : (![0, u 1] : Site 2) ∈ rect 0 n 0 n := by
    rw [mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨by omega, by omega, hub.2.2.1, hub.2.2.2⟩
  have hsub0 : (⟨![0, u 1], hl⟩ : rect 0 n 0 n) =
      ⟨Function.update (![0, u 1] : Site 2) 0
        ((![0, u 1] : Site 2) 0 + ((0 : Nat) : Int)), hseg 0 (Nat.zero_le m)⟩ :=
    Subtype.ext e0.symm
  have hsubm : (⟨u, hu⟩ : rect 0 n 0 n) =
      ⟨Function.update (![0, u 1] : Site 2) 0
        ((![0, u 1] : Site 2) 0 + (m : Int)), hseg m le_rfl⟩ :=
    Subtype.ext em.symm
  refine ⟨hl, ?_⟩
  rw [hsub0, hsubm]
  exact hreach


theorem crr_walk_exit_set_in_box (A B : Set (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y)
    (hw : ∀ z ∈ w.support, z ∈ B) (hx : x ∈ A) (hy : y ∉ A) :
    ∃ a b : Site 2, (hypercubicLattice 2).Adj a b ∧ a ∈ A ∧ b ∉ A ∧ a ∈ B ∧ b ∈ B := by
  induction w with
  | nil => exact absurd hx hy
  | @cons a b c hab p ih =>
      by_cases hb : b ∈ A
      · exact ih (fun z hz => hw z (by simp [hz])) hb hy
      · exact ⟨a, b, hab, hx, hb, hw a (by simp), hw b (by simp)⟩


theorem crr_rightComplement_of_boxMinusL_reachable
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int) {u v : Site 2}
    (hu : u ∈ bac_boxMinusL omega n) (hv : v ∈ bac_boxMinusL omega n)
    (huv : ((hypercubicLattice 2).induce (bac_boxMinusL omega n)).Reachable
      ⟨u, hu⟩ ⟨v, hv⟩)
    (hvR : v ∈ bac_rightComplement omega n) : u ∈ bac_rightComplement omega n := by
  obtain ⟨_hvc, y, hyR, hyc, hvy⟩ := hvR
  exact ⟨hu, y, hyR, hyc, huv.trans hvy⟩


theorem crr_leftFill_reaches_leftReach
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int) {u : Site 2}
    (hu : u ∈ crr_leftFill omega n) :
    ∃ z : Site 2, ∃ hzL : z ∈ bcd_leftReach omega n,
      ((hypercubicLattice 2).induce (crr_leftFill omega n)).Reachable
        ⟨u, hu⟩ ⟨z, ⟨bcd_leftReach_subset_box omega n hzL,
          fun hzR => (bac_rightComplement_mem omega n hzR).2 hzL⟩⟩ := by
  by_cases huL : u ∈ bcd_leftReach omega n
  · exact ⟨u, huL, SimpleGraph.Reachable.refl _⟩
  have huB : u ∈ bac_boxMinusL omega n := ⟨hu.1, huL⟩
  let A : Set (Site 2) := {z | ∃ hz : z ∈ bac_boxMinusL omega n,
    ((hypercubicLattice 2).induce (bac_boxMinusL omega n)).Reachable ⟨u, huB⟩ ⟨z, hz⟩}
  have huA : u ∈ A := ⟨huB, SimpleGraph.Reachable.refl _⟩
  obtain ⟨hlbox, hrow⟩ := crr_leftWall_reaches_boxVertex n hu.1
  let ell : Site 2 := ![0, u 1]
  have hellL : ell ∈ bcd_leftReach omega n := by
    apply jex_leftSide_subset_leftReach omega n
    exact ⟨hlbox, by simp [ell]⟩
  have hellA : ell ∉ A := by
    rintro ⟨hellB, _⟩
    exact hellB.2 hellL
  obtain ⟨wrow⟩ := hrow.symm
  let wrowLat : (hypercubicLattice 2).Walk u ell :=
    wrow.map (SimpleGraph.Embedding.induce (rect 0 n 0 n)).toHom
  have hwbox : ∀ z ∈ wrowLat.support, z ∈ rect 0 n 0 n := by
    intro z hz
    change z ∈ (wrow.map
      (SimpleGraph.Embedding.induce (rect 0 n 0 n)).toHom).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨z', _hz', rfl⟩ := List.mem_map.mp hz
    exact z'.2
  obtain ⟨a, b, hab, haA, hbA, habox, hbbox⟩ :=
    crr_walk_exit_set_in_box A (rect 0 n 0 n) wrowLat hwbox huA hellA
  obtain ⟨haB, hua⟩ := haA
  have hbL : b ∈ bcd_leftReach omega n := by
    by_contra hbL
    have hbB : b ∈ bac_boxMinusL omega n := ⟨hbbox, hbL⟩
    have hstep : ((hypercubicLattice 2).induce (bac_boxMinusL omega n)).Adj
        ⟨a, haB⟩ ⟨b, hbB⟩ := hab
    exact hbA ⟨hbB, hua.trans hstep.reachable⟩
  have haNotR : a ∉ bac_rightComplement omega n := by
    intro haR
    exact hu.2 (crr_rightComplement_of_boxMinusL_reachable omega n huB haB hua haR)
  obtain ⟨pua⟩ := hua
  let puaLat : (hypercubicLattice 2).Walk u a :=
    pua.map (SimpleGraph.Embedding.induce (bac_boxMinusL omega n)).toHom
  have hpuaFill : ∀ z ∈ puaLat.support, z ∈ crr_leftFill omega n := by
    intro z hz
    change z ∈ (pua.map
      (SimpleGraph.Embedding.induce (bac_boxMinusL omega n)).toHom).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
    refine ⟨z'.2.1, ?_⟩
    intro hzR
    have huz := (pua.takeUntil z' hz').reachable
    exact hu.2 (crr_rightComplement_of_boxMinusL_reachable omega n huB z'.2 huz hzR)
  have haFill : a ∈ crr_leftFill omega n := ⟨habox, haNotR⟩
  have huaFill : ((hypercubicLattice 2).induce (crr_leftFill omega n)).Reachable
      ⟨u, hu⟩ ⟨a, haFill⟩ :=
    walk_induce_reachable (hypercubicLattice 2) (crr_leftFill omega n) puaLat
      hpuaFill hu haFill
  have hbFill : b ∈ crr_leftFill omega n :=
    ⟨hbbox, fun hbR => (bac_rightComplement_mem omega n hbR).2 hbL⟩
  have habFill : ((hypercubicLattice 2).induce (crr_leftFill omega n)).Adj
      ⟨a, haFill⟩ ⟨b, hbFill⟩ := hab
  exact ⟨b, hbL, huaFill.trans habFill.reachable⟩


theorem crr_leftFill_connected_pair (omega : ConfigSpace (Sym2 (Site 2))) (n : Int)
    {u v : Site 2} (hu : u ∈ crr_leftFill omega n) (hv : v ∈ crr_leftFill omega n) :
    ((hypercubicLattice 2).induce (crr_leftFill omega n)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
  obtain ⟨zu, hzuL, huz⟩ := crr_leftFill_reaches_leftReach omega n hu
  obtain ⟨zv, hzvL, hvz⟩ := crr_leftFill_reaches_leftReach omega n hv
  have hLR := crr_leftReach_connected_pair omega n hzuL hzvL
  obtain ⟨pLR⟩ := hLR
  let pFill : (hypercubicLattice 2).Walk zu zv :=
    (pLR.map (SimpleGraph.Embedding.induce (bcd_leftReach omega n)).toHom).mapLe
      (fun _ _ h => h)
  have hpFill : ∀ z ∈ pFill.support, z ∈ crr_leftFill omega n := by
    intro z hz
    have hz' : z ∈ (pLR.map
        (SimpleGraph.Embedding.induce (bcd_leftReach omega n)).toHom).support := by
      simpa [pFill] using hz
    rw [SimpleGraph.Walk.support_map] at hz'
    obtain ⟨z', _hz', rfl⟩ := List.mem_map.mp hz'
    exact ⟨bcd_leftReach_subset_box omega n z'.2,
      fun hzR => (bac_rightComplement_mem omega n hzR).2 z'.2⟩
  have hzuFill : zu ∈ crr_leftFill omega n :=
    ⟨bcd_leftReach_subset_box omega n hzuL,
      fun hzR => (bac_rightComplement_mem omega n hzR).2 hzuL⟩
  have hzvFill : zv ∈ crr_leftFill omega n :=
    ⟨bcd_leftReach_subset_box omega n hzvL,
      fun hzR => (bac_rightComplement_mem omega n hzR).2 hzvL⟩
  have hmiddle := walk_induce_reachable (hypercubicLattice 2) (crr_leftFill omega n)
    pFill hpFill hzuFill hzvFill
  exact huz.trans (hmiddle.trans hvz.symm)


theorem crr_rightComplement_connected_induced
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int)
    (hnoH : ¬ HorizontalCrossing omega 0 n 0 n) {u v : Site 2}
    (hu : u ∈ bac_rightComplement omega n) (hv : v ∈ bac_rightComplement omega n) :
    ((hypercubicLattice 2).induce (bac_rightComplement omega n)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
  obtain ⟨huB, hvB, huv⟩ := rcm_rightComplement_connected_pair omega n hnoH hu hv
  obtain ⟨p⟩ := huv
  let pLat : (hypercubicLattice 2).Walk u v :=
    p.map (SimpleGraph.Embedding.induce (bac_boxMinusL omega n)).toHom
  have hpR : ∀ z ∈ pLat.support, z ∈ bac_rightComplement omega n := by
    intro z hz
    change z ∈ (p.map
      (SimpleGraph.Embedding.induce (bac_boxMinusL omega n)).toHom).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
    have hzv := (p.dropUntil z' hz').reachable
    exact crr_rightComplement_of_boxMinusL_reachable omega n z'.2 hvB hzv hv
  exact walk_induce_reachable (hypercubicLattice 2) (bac_rightComplement omega n)
    pLat hpR hu hv


end Universality
end StatMech
