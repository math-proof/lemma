/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusAxisBlockAverage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusAxisMonotonicity
import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredBlockAverage
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusAxisBlockAverage
open Finset Set
open scoped BigOperators


namespace StatMech.FrontierA

variable {Gamma : Type*} [AddCommGroup Gamma]


section FiniteGreen

variable [Fintype Gamma]


theorem block_character_re_double_sum
    (B : Finset Gamma) (chi : AddChar Gamma Complex) :
    (∑ a ∈ B, ∑ b ∈ B,
        (starRingEnd Complex (chi (b - a))).re) =
      Complex.normSq (∑ a ∈ B, chi a) := by
  have hterm (a b : Gamma) :
      starRingEnd Complex (chi (b - a)) =
        chi a * starRingEnd Complex (chi b) := by
    rw [AddChar.map_sub_eq_div, map_div₀, div_eq_mul_inv]
    have hinv : (starRingEnd Complex (chi a))⁻¹ = chi a := by
      rw [← AddChar.inv_apply_eq_conj]
      exact inv_inv (chi a)
    rw [hinv]
    ring
  have hcomplex :
      (∑ a ∈ B, ∑ b ∈ B,
          starRingEnd Complex (chi (b - a))) =
        Complex.normSq (∑ a ∈ B, chi a) := by
    simp_rw [hterm, ← Finset.mul_sum]
    rw [← Finset.sum_mul, ← map_sum (starRingEnd Complex),
      Complex.mul_conj]
  have hre := congrArg Complex.re hcomplex
  change Complex.reCLM
      (∑ a ∈ B, ∑ b ∈ B,
        starRingEnd Complex (chi (b - a))) = _ at hre
  simp only [map_sum] at hre
  exact hre


theorem finiteTorusBlockDifferenceAverage_zeroModeGreen
    (dispersion : AddChar Gamma Complex → Real) (B : Finset Gamma) :
    finiteTorusBlockDifferenceAverage
        (finiteTorusZeroModeGreen dispersion) B =
      (1 / Fintype.card Gamma : Real) *
        ∑ chi ∈ Finset.univ.erase (0 : AddChar Gamma Complex),
          (dispersion chi)⁻¹ * finiteTorusBlockCharacterWeight B chi := by
  classical
  by_cases hB : B.card = 0
  · simp [finiteTorusBlockDifferenceAverage,
      finiteTorusBlockCharacterWeight, hB]
  · have hBReal : (B.card : Real) ≠ 0 := by exact_mod_cast hB
    have hraw :
        (∑ a ∈ B, ∑ b ∈ B,
            finiteTorusZeroModeGreen dispersion (b - a)) =
          (1 / Fintype.card Gamma : Real) *
            ∑ chi ∈ Finset.univ.erase (0 : AddChar Gamma Complex),
              (dispersion chi)⁻¹ *
                Complex.normSq (∑ a ∈ B, chi a) := by
      unfold finiteTorusZeroModeGreen
      calc
        (∑ a ∈ B, ∑ b ∈ B,
            (1 / Fintype.card Gamma : Real) *
              ∑ chi ∈ Finset.univ.erase (0 : AddChar Gamma Complex),
                (starRingEnd Complex (chi (b - a))).re / dispersion chi) =
            (∑ a ∈ B, ∑ b ∈ B,
              ∑ chi ∈ Finset.univ.erase (0 : AddChar Gamma Complex),
                (1 / Fintype.card Gamma : Real) *
                  ((starRingEnd Complex (chi (b - a))).re /
                    dispersion chi)) := by
              apply Finset.sum_congr rfl
              intro a ha
              apply Finset.sum_congr rfl
              intro b hb
              rw [Finset.mul_sum]
        _ = ∑ a ∈ B,
              ∑ chi ∈ Finset.univ.erase (0 : AddChar Gamma Complex),
                ∑ b ∈ B, (1 / Fintype.card Gamma : Real) *
                  ((starRingEnd Complex (chi (b - a))).re /
                    dispersion chi) := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [Finset.sum_comm]
        _ = ∑ chi ∈ Finset.univ.erase
              (0 : AddChar Gamma Complex),
              ∑ a ∈ B, ∑ b ∈ B,
                (1 / Fintype.card Gamma : Real) *
                  ((starRingEnd Complex (chi (b - a))).re /
                    dispersion chi) := by
              rw [Finset.sum_comm]
        _ = ∑ chi ∈ Finset.univ.erase (0 : AddChar Gamma Complex),
              (1 / Fintype.card Gamma : Real) *
                ((dispersion chi)⁻¹ *
                  Complex.normSq (∑ a ∈ B, chi a)) := by
              apply Finset.sum_congr rfl
              intro chi hchi
              calc
                (∑ a ∈ B, ∑ b ∈ B,
                    (1 / Fintype.card Gamma : Real) *
                      ((starRingEnd Complex (chi (b - a))).re /
                        dispersion chi)) =
                    (1 / Fintype.card Gamma : Real) * (dispersion chi)⁻¹ *
                      (∑ a ∈ B, ∑ b ∈ B,
                        (starRingEnd Complex (chi (b - a))).re) := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro a ha
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro b hb
                  ring
                _ = (1 / Fintype.card Gamma : Real) *
                    ((dispersion chi)⁻¹ *
                      Complex.normSq (∑ a ∈ B, chi a)) := by
                  rw [block_character_re_double_sum]
                  ring
        _ = (1 / Fintype.card Gamma : Real) *
            ∑ chi ∈ Finset.univ.erase (0 : AddChar Gamma Complex),
              (dispersion chi)⁻¹ *
                Complex.normSq (∑ a ∈ B, chi a) := by
              exact (Finset.mul_sum
                (Finset.univ.erase (0 : AddChar Gamma Complex))
                (fun chi => (dispersion chi)⁻¹ *
                  Complex.normSq (∑ a ∈ B, chi a))
                (1 / Fintype.card Gamma : Real)).symm
    unfold finiteTorusBlockDifferenceAverage
    rw [hraw]
    unfold finiteTorusBlockCharacterWeight
    have hscaled :
        (∑ chi ∈ Finset.univ.erase (0 : AddChar Gamma Complex),
            (dispersion chi)⁻¹ *
              (Complex.normSq (∑ a ∈ B, chi a) / (B.card : Real) ^ 2)) =
          (1 / (B.card : Real) ^ 2) *
            ∑ chi ∈ Finset.univ.erase (0 : AddChar Gamma Complex),
              (dispersion chi)⁻¹ *
                Complex.normSq (∑ a ∈ B, chi a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro chi hchi
      field_simp
    rw [hscaled]
    ring

end FiniteGreen

variable {d k : Nat}


theorem finiteTorusZeroModeGreen_isingSiteToDyadicTorus
    (x : StatMech.Lattice.Site d) :
    finiteTorusZeroModeGreen
        (isingTorusCharacterDispersion (d := d) (k := k))
        (isingSiteToDyadicTorus k x) =
      isingDyadicTorusGreen x k := by
  classical
  let f : AddChar (IsingDyadicTorus d k) Complex → Real := fun chi =>
    (starRingEnd Complex (chi (isingSiteToDyadicTorus k x))).re /
      isingTorusCharacterDispersion chi
  have hfzero : f 0 = 0 := by
    simp [f, isingTorusCharacterDispersion]
  have herase :
      (∑ chi ∈ Finset.univ.erase
          (0 : AddChar (IsingDyadicTorus d k) Complex), f chi) =
        ∑ chi : AddChar (IsingDyadicTorus d k) Complex, f chi := by
    rw [← Finset.sum_erase_add Finset.univ f (Finset.mem_univ 0), hfzero,
      add_zero]
  have hreindex := (isingTorusMomentumEquiv (d := d) (k := k)).sum_comp f
  rw [finiteTorusZeroModeGreen, herase, ← hreindex,
    isingDyadicTorusGreen_eq_character_sum]
  apply congrArg ((1 / Fintype.card (IsingDyadicTorus d k) : Real) * ·)
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hp0 : p = 0
  · subst p
    simp [f, isingTorusCharacterDispersion]
  · simp only [if_neg hp0]
    rw [show f (isingTorusMomentumEquiv p) =
        (starRingEnd Complex
          (isingTorusMomentumChar p (isingSiteToDyadicTorus k x))).re /
            isingTorusCharacterDispersion (isingTorusMomentumChar p) by rfl]
    ring


theorem finiteTorusZeroModeGreen_axisDifference
    (i : Fin d) (a b : Nat) :
    finiteTorusZeroModeGreen
        (isingTorusCharacterDispersion (d := d) (k := k))
        (isingTorusCoordinateShift i b - isingTorusCoordinateShift i a) =
      isingDyadicTorusGreen
        (Pi.single i ((b : Int) - (a : Int))) k := by
  rw [← finiteTorusZeroModeGreen_isingSiteToDyadicTorus
    (k := k) (Pi.single i ((b : Int) - (a : Int)))]
  congr 1
  funext j
  by_cases hji : j = i
  · subst j
    simp only [Pi.sub_apply, isingTorusCoordinateShift_apply_same,
      isingSiteToDyadicTorus, Pi.single_eq_same]
    push_cast
    rfl
  · simp only [Pi.sub_apply,
      isingTorusCoordinateShift_apply_of_ne i j hji,
      isingSiteToDyadicTorus, Pi.single_eq_of_ne hji]
    change (0 : ZMod (2 ^ (k + 2))) - 0 = ((0 : Int) : ZMod (2 ^ (k + 2)))
    norm_num


end StatMech.FrontierA
