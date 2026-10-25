/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusAxisBlockAverage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusAxisMonotonicity
import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredBlockAverage
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusAxisBlockAverage.Part3
open Finset Set
open scoped BigOperators


namespace StatMech.FrontierA

variable {Gamma : Type*} [AddCommGroup Gamma]


variable {d k : Nat}


theorem isingTorusSparseAxisBlock_nonempty
    (i : Fin d) (spacing count : Nat) (hcount : 0 < count) :
    (isingTorusSparseAxisBlock (k := k) i spacing count).Nonempty := by
  refine ⟨isingTorusCoordinateShift i 0, ?_⟩
  rw [isingTorusSparseAxisBlock, Finset.mem_image]
  refine ⟨0, by simp [hcount], ?_⟩
  simp

theorem isingTorusSparseAxisBlock_card
    (i : Fin d) (spacing count : Nat) (hspacing : 0 < spacing)
    (hr : (count - 1) * spacing < isingDyadicSide k) :
    (isingTorusSparseAxisBlock (k := k) i spacing count).card = count := by
  unfold isingTorusSparseAxisBlock
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro a ha b hb hab
    have haCount : a < count := by simpa using ha
    have hbCount : b < count := by simpa using hb
    have haEnd : a * spacing < (count - 1) * spacing + 1 := by
      apply Nat.lt_succ_of_le
      exact Nat.mul_le_mul_right spacing (by omega)
    have hbEnd : b * spacing < (count - 1) * spacing + 1 := by
      apply Nat.lt_succ_of_le
      exact Nat.mul_le_mul_right spacing (by omega)
    have hmul := isingTorusCoordinateShift_injectiveOn_range
      (k := k) i ((count - 1) * spacing) hr
      (by simpa using haEnd) (by simpa using hbEnd) hab
    exact Nat.eq_of_mul_eq_mul_right hspacing hmul


theorem finiteTorusBlockDifferenceAverage_zeroModeGreen_sparseAxis
    (i : Fin d) (spacing count : Nat) (hspacing : 0 < spacing)
    (hr : (count - 1) * spacing < isingDyadicSide k) :
    finiteTorusBlockDifferenceAverage
        (finiteTorusZeroModeGreen
          (isingTorusCharacterDispersion (d := d) (k := k)))
        (isingTorusSparseAxisBlock i spacing count) =
      (1 / (count : Real) ^ 2) *
        ∑ a ∈ Finset.range count,
          ∑ b ∈ Finset.range count,
            isingDyadicTorusGreen
              (Pi.single i (((b * spacing : Nat) : Int) -
                ((a * spacing : Nat) : Int))) k := by
  unfold finiteTorusBlockDifferenceAverage
  rw [isingTorusSparseAxisBlock_card i spacing count hspacing hr]
  apply congrArg ((1 / (count : Real) ^ 2) * ·)
  unfold isingTorusSparseAxisBlock
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro b hb
      exact finiteTorusZeroModeGreen_axisDifference
        i (a * spacing) (b * spacing)
    · intro b hb c hc hbc
      have hbCount : b < count := by simpa using hb
      have hcCount : c < count := by simpa using hc
      have hbEnd : b * spacing < (count - 1) * spacing + 1 := by
        apply Nat.lt_succ_of_le
        exact Nat.mul_le_mul_right spacing (by omega)
      have hcEnd : c * spacing < (count - 1) * spacing + 1 := by
        apply Nat.lt_succ_of_le
        exact Nat.mul_le_mul_right spacing (by omega)
      have hmul := isingTorusCoordinateShift_injectiveOn_range
        (k := k) i ((count - 1) * spacing) hr
        (by simpa using hbEnd) (by simpa using hcEnd) hbc
      exact Nat.eq_of_mul_eq_mul_right hspacing hmul
  · intro a ha b hb hab
    have haCount : a < count := by simpa using ha
    have hbCount : b < count := by simpa using hb
    have haEnd : a * spacing < (count - 1) * spacing + 1 := by
      apply Nat.lt_succ_of_le
      exact Nat.mul_le_mul_right spacing (by omega)
    have hbEnd : b * spacing < (count - 1) * spacing + 1 := by
      apply Nat.lt_succ_of_le
      exact Nat.mul_le_mul_right spacing (by omega)
    have hmul := isingTorusCoordinateShift_injectiveOn_range
      (k := k) i ((count - 1) * spacing) hr
      (by simpa using haEnd) (by simpa using hbEnd) hab
    exact Nat.eq_of_mul_eq_mul_right hspacing hmul


theorem finiteTorusBlockDifferenceAverage_zeroModeGreen_sparseAxis_le
    (i : Fin d) (spacing count : Nat) (hspacing : 0 < spacing)
    (hcount : 0 < count)
    (hr : (count - 1) * spacing < isingDyadicSide k)
    (M epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (hzero : |isingDyadicTorusGreen (0 : StatMech.Lattice.Site d) k| ≤ M)
    (hoff : ∀ a ∈ Finset.range count, ∀ b ∈ Finset.range count,
      a ≠ b →
        |isingDyadicTorusGreen
          (Pi.single i (((b * spacing : Nat) : Int) -
            ((a * spacing : Nat) : Int))) k| ≤ epsilon) :
    finiteTorusBlockDifferenceAverage
        (finiteTorusZeroModeGreen
          (isingTorusCharacterDispersion (d := d) (k := k)))
        (isingTorusSparseAxisBlock i spacing count) ≤
      M / count + epsilon := by
  rw [finiteTorusBlockDifferenceAverage_zeroModeGreen_sparseAxis
    i spacing count hspacing hr]
  let G : Nat → Nat → Real := fun a b =>
    isingDyadicTorusGreen
      (Pi.single i (((b * spacing : Nat) : Int) -
        ((a * spacing : Nat) : Int))) k
  have hinner (a : Nat) (ha : a ∈ Finset.range count) :
      ∑ b ∈ Finset.range count, G a b ≤
        M + (count : Real) * epsilon := by
    have hoff' : ∑ b ∈ (Finset.range count).erase a, |G a b| ≤
        ∑ _b ∈ (Finset.range count).erase a, epsilon := by
      apply Finset.sum_le_sum
      intro b hb
      exact hoff a ha b (Finset.mem_of_mem_erase hb)
        (Finset.ne_of_mem_erase hb).symm
    have hsumAbs : ∑ b ∈ Finset.range count, |G a b| ≤
        M + (count : Real) * epsilon := by
      have hdiag : |G a a| ≤ M := by
        simpa [G] using hzero
      rw [← Finset.sum_erase_add _ _ ha]
      calc
        (∑ b ∈ (Finset.range count).erase a, |G a b|) + |G a a| ≤
            (∑ _b ∈ (Finset.range count).erase a, epsilon) + M :=
          add_le_add hoff' hdiag
        _ ≤ M + (count : Real) * epsilon := by
          have hcard : ((Finset.range count).erase a).card ≤ count := by
            simpa using (Finset.card_erase_le :
              ((Finset.range count).erase a).card ≤
                (Finset.range count).card)
          simp only [Finset.sum_const, nsmul_eq_mul]
          have hmul := mul_le_mul_of_nonneg_right
            (show (((Finset.range count).erase a).card : Real) ≤ count by
              exact_mod_cast hcard) hepsilon
          linarith
    exact (Finset.sum_le_sum fun b _ => le_abs_self (G a b)).trans hsumAbs
  have hsum :
      ∑ a ∈ Finset.range count, ∑ b ∈ Finset.range count, G a b ≤
        (count : Real) * (M + (count : Real) * epsilon) := by
    calc
      ∑ a ∈ Finset.range count, ∑ b ∈ Finset.range count, G a b ≤
          ∑ _a ∈ Finset.range count,
            (M + (count : Real) * epsilon) := by
        apply Finset.sum_le_sum
        intro a ha
        exact hinner a ha
      _ = (count : Real) * (M + (count : Real) * epsilon) := by
        simp
        ring
  change (1 / (count : Real) ^ 2) *
      (∑ a ∈ Finset.range count, ∑ b ∈ Finset.range count, G a b) ≤ _
  calc
    (1 / (count : Real) ^ 2) *
        (∑ a ∈ Finset.range count, ∑ b ∈ Finset.range count, G a b) ≤
      (1 / (count : Real) ^ 2) *
        ((count : Real) * (M + (count : Real) * epsilon)) := by
          gcongr
    _ = M / count + epsilon := by
      have hc : (count : Real) ≠ 0 := by exact_mod_cast hcount.ne'
      field_simp


theorem isingTorusTwoPoint_axis_antitone
    (i : Fin d) (beta : Real) (hbeta : 0 ≤ beta)
    {a b : Nat} (hab : a ≤ b) (hb : b ≤ 2 ^ (k + 1)) :
    isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i b) ≤
      isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i a) := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
      exact (isingTorusAxisCorrelation_succ_le
        (k := k) i beta hbeta b (by omega)).trans (ih (by omega))

theorem isingTorusCoordinateShift_sub_of_le
    (i : Fin d) {a b : Nat} (hab : a ≤ b) :
    isingTorusCoordinateShift (k := k) i b -
        isingTorusCoordinateShift i a =
      isingTorusCoordinateShift i (b - a) := by
  have hadd := isingTorusCoordinateShift_add (k := k) i a (b - a)
  rw [Nat.add_sub_of_le hab] at hadd
  rw [hadd]
  abel


theorem isingTorusTwoPoint_axisEndpoint_le_difference
    (i : Fin d) (beta : Real) (hbeta : 0 ≤ beta)
    (r : Nat) (hr : r ≤ 2 ^ (k + 1))
    {a b : Nat} (ha : a < r + 1) (hb : b < r + 1) :
    isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i r) ≤
      isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i b -
          isingTorusCoordinateShift i a) := by
  rcases le_total a b with hab | hba
  · rw [isingTorusCoordinateShift_sub_of_le i hab]
    exact isingTorusTwoPoint_axis_antitone i beta hbeta
      (Nat.sub_le b a |>.trans (by omega)) hr
  · have hsub := isingTorusCoordinateShift_sub_of_le
      (k := k) i hba
    have hneg : isingTorusCoordinateShift (k := k) i b -
          isingTorusCoordinateShift i a =
        -isingTorusCoordinateShift i (a - b) := by
      calc
        isingTorusCoordinateShift (k := k) i b -
            isingTorusCoordinateShift i a =
          -(isingTorusCoordinateShift i a -
            isingTorusCoordinateShift i b) := by abel
        _ = -isingTorusCoordinateShift i (a - b) :=
          congrArg Neg.neg hsub
    rw [hneg, isingTorusTwoPoint_origin_neg]
    exact isingTorusTwoPoint_axis_antitone i beta hbeta
      (Nat.sub_le a b |>.trans (by omega)) hr


theorem isingTorusTwoPoint_sparseAxisEndpoint_le_difference
    (i : Fin d) (beta : Real) (hbeta : 0 ≤ beta)
    (spacing count : Nat) (hcount : 0 < count)
    (hr : (count - 1) * spacing ≤ 2 ^ (k + 1))
    {a b : Nat} (ha : a < count) (hb : b < count) :
    isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i ((count - 1) * spacing)) ≤
      isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i (b * spacing) -
          isingTorusCoordinateShift i (a * spacing)) := by
  apply isingTorusTwoPoint_axisEndpoint_le_difference
    i beta hbeta ((count - 1) * spacing) hr
  · apply Nat.lt_succ_of_le
    exact Nat.mul_le_mul_right spacing (by omega)
  · apply Nat.lt_succ_of_le
    exact Nat.mul_le_mul_right spacing (by omega)


theorem isingTorusTwoPoint_axisEndpoint_le_greenBlockAverage_of_block
    (i : Fin d) (beta : Real) (hbeta : 0 < beta) (r : Nat)
    (B : Finset (IsingDyadicTorus d k)) (hB : B.Nonempty)
    (hlower : ∀ a ∈ B, ∀ b ∈ B,
      isingTorusTwoPoint (k := k) beta 0
          (isingTorusCoordinateShift i r) ≤
        isingTorusTwoPoint (k := k) beta 0 (b - a)) :
    isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i r) ≤
      (finiteTorusFourierCoeff
          (fun z : IsingDyadicTorus d k => isingTorusTwoPoint beta 0 z) 0).re /
        Fintype.card (IsingDyadicTorus d k) +
      (1 / beta) * finiteTorusBlockDifferenceAverage
        (finiteTorusZeroModeGreen (Gamma := IsingDyadicTorus d k)
          (isingTorusCharacterDispersion (d := d) (k := k))) B := by
  let G : IsingDyadicTorus d k → Real :=
    fun z => isingTorusTwoPoint beta 0 z
  have hkernel : G = isingTorusAveragedTwoPoint beta := by
    funext z
    exact (isingTorusAveragedTwoPoint_eq_twoPoint beta z).symm
  have hblockLower :
      isingTorusTwoPoint beta 0 (isingTorusCoordinateShift i r) ≤
        finiteTorusBlockDifferenceAverage G B :=
    le_finiteTorusBlockDifferenceAverage G B _ hB hlower
  have hblockUpper := finiteTorusBlockDifferenceAverage_le
    G B (1 / beta) isingTorusCharacterDispersion hB
      (fun chi => by
        rw [hkernel, finiteTorusFourierCoeff_isingTorusAveragedTwoPoint]
        rfl)
      (fun chi hchi => by
        rw [hkernel]
        have hdisp := isingTorusCharacterDispersion_pos_of_ne_zero chi hchi
        have hbound := isingTorusAveragedTwoPoint_fourier_bound beta hbeta
          (isingTorus_gaussianDominated beta hbeta.le) chi hdisp
        convert hbound using 1 <;> ring)
  have hgreen := finiteTorusBlockDifferenceAverage_zeroModeGreen
    (isingTorusCharacterDispersion (d := d) (k := k)) B
  rw [hgreen]
  refine hblockLower.trans (hblockUpper.trans_eq ?_)
  simp only [G]
  congr 1
  have hsum :
      (∑ chi ∈ Finset.univ.erase
          (0 : AddChar (IsingDyadicTorus d k) Complex),
        ((1 / beta) / isingTorusCharacterDispersion chi) *
          finiteTorusBlockCharacterWeight B chi) =
        (1 / beta) *
          ∑ chi ∈ Finset.univ.erase
            (0 : AddChar (IsingDyadicTorus d k) Complex),
          (isingTorusCharacterDispersion chi)⁻¹ *
            finiteTorusBlockCharacterWeight B chi := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro chi hchi
    ring
  rw [hsum]
  ring


theorem isingTorusTwoPoint_sparseAxisEndpoint_le_greenBlockAverage
    (i : Fin d) (beta : Real) (hbeta : 0 < beta)
    (spacing count : Nat) (hcount : 0 < count)
    (hr : (count - 1) * spacing ≤ 2 ^ (k + 1)) :
    isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i ((count - 1) * spacing)) ≤
      (finiteTorusFourierCoeff
          (fun z : IsingDyadicTorus d k => isingTorusTwoPoint beta 0 z) 0).re /
        Fintype.card (IsingDyadicTorus d k) +
      (1 / beta) * finiteTorusBlockDifferenceAverage
        (finiteTorusZeroModeGreen (Gamma := IsingDyadicTorus d k)
          (isingTorusCharacterDispersion (d := d) (k := k)))
        (isingTorusSparseAxisBlock (k := k) i spacing count) := by
  apply isingTorusTwoPoint_axisEndpoint_le_greenBlockAverage_of_block
    i beta hbeta ((count - 1) * spacing)
    (isingTorusSparseAxisBlock i spacing count)
    (isingTorusSparseAxisBlock_nonempty i spacing count hcount)
  intro a ha b hb
  rw [isingTorusSparseAxisBlock, Finset.mem_image] at ha hb
  obtain ⟨aIndex, haIndex, rfl⟩ := ha
  obtain ⟨bIndex, hbIndex, rfl⟩ := hb
  exact isingTorusTwoPoint_sparseAxisEndpoint_le_difference
    i beta hbeta.le spacing count hcount hr
      (by simpa using haIndex) (by simpa using hbIndex)


theorem isingTorusTwoPoint_axisEndpoint_le_blockDifferenceAverage
    (i : Fin d) (beta : Real) (hbeta : 0 ≤ beta)
    (r : Nat) (hr : r ≤ 2 ^ (k + 1)) :
    isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i r) ≤
      finiteTorusBlockDifferenceAverage
        (fun z : IsingDyadicTorus d k => isingTorusTwoPoint beta 0 z)
        (isingTorusAxisSegment i r) := by
  apply le_finiteTorusBlockDifferenceAverage _ _ _
    (isingTorusAxisSegment_nonempty i r)
  intro a ha b hb
  rw [isingTorusAxisSegment, Finset.mem_image] at ha hb
  obtain ⟨aIndex, haIndex, rfl⟩ := ha
  obtain ⟨bIndex, hbIndex, rfl⟩ := hb
  exact isingTorusTwoPoint_axisEndpoint_le_difference
    i beta hbeta r hr (by simpa using haIndex) (by simpa using hbIndex)


theorem isingTorusTwoPoint_axisEndpoint_le_fourierBlockBound
    (i : Fin d) (beta : Real) (hbeta : 0 < beta)
    (r : Nat) (hr : r ≤ 2 ^ (k + 1)) :
    isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i r) ≤
      (finiteTorusFourierCoeff
          (fun z : IsingDyadicTorus d k => isingTorusTwoPoint beta 0 z) 0).re /
        Fintype.card (IsingDyadicTorus d k) +
      (1 / Fintype.card (IsingDyadicTorus d k) : Real) *
        ∑ chi ∈ Finset.univ.erase
            (0 : AddChar (IsingDyadicTorus d k) Complex),
          ((1 / beta) / isingTorusCharacterDispersion chi) *
            finiteTorusBlockCharacterWeight
              (isingTorusAxisSegment i r) chi := by
  let G : IsingDyadicTorus d k → Real :=
    fun z => isingTorusTwoPoint beta 0 z
  have hkernel : G = isingTorusAveragedTwoPoint beta := by
    funext z
    exact (isingTorusAveragedTwoPoint_eq_twoPoint beta z).symm
  have hlower :=
    isingTorusTwoPoint_axisEndpoint_le_blockDifferenceAverage
      (k := k) i beta hbeta.le r hr
  have hupper := finiteTorusBlockDifferenceAverage_le
    G (isingTorusAxisSegment i r) (1 / beta)
      isingTorusCharacterDispersion
      (isingTorusAxisSegment_nonempty i r)
      (fun chi => by
        rw [hkernel, finiteTorusFourierCoeff_isingTorusAveragedTwoPoint]
        rfl)
      (fun chi hchi => by
        rw [hkernel]
        have hdisp := isingTorusCharacterDispersion_pos_of_ne_zero chi hchi
        have hbound := isingTorusAveragedTwoPoint_fourier_bound beta hbeta
          (isingTorus_gaussianDominated beta hbeta.le) chi hdisp
        convert hbound using 1 <;> ring)
  exact hlower.trans (by simpa only [G] using hupper)


theorem isingTorusTwoPoint_axisEndpoint_le_greenBlockAverage
    (i : Fin d) (beta : Real) (hbeta : 0 < beta)
    (r : Nat) (hr : r ≤ 2 ^ (k + 1)) :
    isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i r) ≤
      (finiteTorusFourierCoeff
          (fun z : IsingDyadicTorus d k => isingTorusTwoPoint beta 0 z) 0).re /
        Fintype.card (IsingDyadicTorus d k) +
      (1 / beta) * finiteTorusBlockDifferenceAverage
        (finiteTorusZeroModeGreen (Gamma := IsingDyadicTorus d k)
          (isingTorusCharacterDispersion (d := d) (k := k)))
        (isingTorusAxisSegment (k := k) i r) := by
  have hbound := isingTorusTwoPoint_axisEndpoint_le_fourierBlockBound
    (k := k) i beta hbeta r hr
  have hgreen := finiteTorusBlockDifferenceAverage_zeroModeGreen
    (isingTorusCharacterDispersion (d := d) (k := k))
    (isingTorusAxisSegment (k := k) i r)
  rw [hgreen]
  exact hbound.trans_eq (by
    congr 1
    have hsum :
        (∑ chi ∈ Finset.univ.erase
            (0 : AddChar (IsingDyadicTorus d k) Complex),
          ((1 / beta) / isingTorusCharacterDispersion chi) *
            finiteTorusBlockCharacterWeight
              (isingTorusAxisSegment i r) chi) =
          (1 / beta) *
            ∑ chi ∈ Finset.univ.erase
              (0 : AddChar (IsingDyadicTorus d k) Complex),
            (isingTorusCharacterDispersion chi)⁻¹ *
              finiteTorusBlockCharacterWeight
                (isingTorusAxisSegment i r) chi := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro chi hchi
      ring
    rw [hsum]
    ring)

end StatMech.FrontierA
