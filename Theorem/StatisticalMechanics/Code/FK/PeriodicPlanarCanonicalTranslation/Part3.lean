/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalFKG
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQTranslation.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalTranslation.Part5
open Filter MeasureTheory Set SimpleGraph Topology
open scoped BigOperators


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]

theorem PeriodicGraph.shiftedFreeMultiMass_eq_centered
    (P : PeriodicGraph V) (z : Site 2) (N : Nat)
    (t : Finset (Sym2 (P.BufferedVertex N)))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (m : Nat) (hNm : N ≤ m) :
    P.shiftedFreeMultiMass z N t p q m hNm =
      (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real
        (fmu_multiOpen (t.image (P.edgeIncl (P.bufferedRadius N)))) := by
  let tm := t.image (Sym2.map (P.bufferedVertexInclLE hNm))
  have hglobal : tm.image (P.edgeIncl (P.bufferedRadius m)) =
      t.image (P.edgeIncl (P.bufferedRadius N)) := by
    dsimp only [tm]
    rw [Finset.image_image]
    apply Finset.image_congr
    intro e he
    exact P.edgeIncl_bufferedVertexInclLE hNm e
  rw [← hglobal]
  rw [P.freeBufferedMeasure_real_multiOpen m hp hp1
    (zero_lt_one.trans_le hq) tm]
  have hiso := P.centered_eq_shifted_free_multiMass z m tm p q
  unfold PeriodicGraph.shiftedFreeMultiMass
  exact hiso.symm

theorem PeriodicGraph.shiftedFreeMultiMass_le_centered_shift
    (P : PeriodicGraph V) (z : Site 2) (N : Nat)
    (t : Finset (Sym2 (P.BufferedVertex N)))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (m : Nat) (hNm : N ≤ m) :
    P.shiftedFreeMultiMass z N t p q m hNm ≤
      (P.freeBufferedMeasure (m + flc_vrad z) hp hp1
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real
        (fmu_multiOpen ((t.image (P.edgeIncl (P.bufferedRadius N))).image
          (Sym2.map (P.shift z)))) := by
  let tm := t.image (Sym2.map (P.bufferedVertexInclLE hNm))
  let hsub := P.shiftedBuffered_subset_buffered z m
  have hdom := P.shifted_free_multiMass_le_buffered z m
    (m + flc_vrad z) hsub hp hp1 hq
    (tm.image (Sym2.map (P.shiftBufferedEquiv z m)))
  rw [← P.freeBufferedMeasure_real_multiOpen (m + flc_vrad z)
    hp hp1 (zero_lt_one.trans_le hq)] at hdom
  refine hdom.trans_eq ?_
  congr 2
  simp only [tm, Finset.image_image]
  apply Finset.image_congr
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y => rfl

theorem PeriodicGraph.centered_shift_le_shiftedFreeMultiMass
    (P : PeriodicGraph V) (z : Site 2) (N : Nat)
    (t : Finset (Sym2 (P.BufferedVertex N)))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (m a : Nat) (hNm : N ≤ m) (ha : a + flc_vrad z ≤ m)
    (ta : Finset (Sym2 (P.BufferedVertex a)))
    (hta : ta.image (P.edgeIncl (P.bufferedRadius a)) =
      (t.image (P.edgeIncl (P.bufferedRadius N))).image
        (Sym2.map (P.shift z))) :
    (P.freeBufferedMeasure a hp hp1 (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 V))).real
        (fmu_multiOpen ((t.image (P.edgeIncl (P.bufferedRadius N))).image
          (Sym2.map (P.shift z)))) ≤
      P.shiftedFreeMultiMass z N t p q m hNm := by
  let tm := t.image (Sym2.map (P.bufferedVertexInclLE hNm))
  let hsub := P.buffered_subset_shiftedBuffered z ha
  have hdom := P.buffered_free_multiMass_le_shifted z a m hsub
    hp hp1 hq ta
  rw [← P.freeBufferedMeasure_real_multiOpen a hp hp1
    (zero_lt_one.trans_le hq), hta] at hdom
  have hedge : ta.image
      (ocd_innerEdge (P.bufferedToShiftedIncl z a m hsub)) =
      (tm.image (Sym2.map (P.shiftBufferedEquiv z m))) := by
    apply Finset.image_injective
      (Sym2.map.injective (f := (Subtype.val :
        P.ShiftedBufferedVertex z m → V)) Subtype.val_injective)
    rw [Finset.image_image, Finset.image_image]
    calc
      ta.image ((Sym2.map (Subtype.val : P.ShiftedBufferedVertex z m → V)) ∘
          ocd_innerEdge (P.bufferedToShiftedIncl z a m hsub)) =
          ta.image (P.edgeIncl (P.bufferedRadius a)) := by
            apply Finset.image_congr
            intro e he
            induction e using Sym2.inductionOn with
            | _ x y => rfl
      _ = (t.image (P.edgeIncl (P.bufferedRadius N))).image
          (Sym2.map (P.shift z)) := hta
      _ = tm.image ((Sym2.map (Subtype.val : P.ShiftedBufferedVertex z m → V)) ∘
          Sym2.map (P.shiftBufferedEquiv z m)) := by
            simp only [tm, Finset.image_image]
            apply Finset.image_congr
            intro e he
            induction e using Sym2.inductionOn with
            | _ x y => rfl
  refine hdom.trans_eq ?_
  unfold PeriodicGraph.shiftedFreeMultiMass
  rw [hedge]

theorem isClopen_fmu_multiOpen (T : Finset (Sym2 V)) :
    IsClopen (fmu_multiOpen T) := by
  have heq : fmu_multiOpen T = cylinder T
      {eta : ∀ _e : T, Bool | ∀ e : T, eta e = true} := by
    ext omega
    simp only [fmu_multiOpen, Set.mem_setOf_eq, cylinder, Set.mem_preimage]
    constructor
    · intro h e
      exact h e.1 e.2
    · intro h e he
      exact h ⟨e, he⟩
  rw [heq]
  exact isClopen_cylinderEvent T _

end StatMech.FK.PeriodicPlanar
