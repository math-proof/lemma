/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusAxisBlockAverage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusAxisMonotonicity
import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredBlockAverage
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusAxisBlockAverage.Part2
open Finset Set
open scoped BigOperators


namespace StatMech.FrontierA

variable {Gamma : Type*} [AddCommGroup Gamma]


variable {d k : Nat}


theorem isingTorusCoordinateShift_injectiveOn_range
    (i : Fin d) (r : Nat) (hr : r < isingDyadicSide k) :
    Set.InjOn (isingTorusCoordinateShift (k := k) i)
      (Finset.range (r + 1) : Set Nat) := by
  intro a ha b hb hab
  have haR : a < r + 1 := by simpa using ha
  have hbR : b < r + 1 := by simpa using hb
  have haL : a < isingDyadicSide k := by omega
  have hbL : b < isingDyadicSide k := by omega
  have hcoord := congrFun hab i
  rw [isingTorusCoordinateShift_apply_same,
    isingTorusCoordinateShift_apply_same] at hcoord
  have hval := congrArg ZMod.val hcoord
  have haMod : a < 2 ^ (k + 2) := by
    simpa [isingDyadicSide] using haL
  have hbMod : b < 2 ^ (k + 2) := by
    simpa [isingDyadicSide] using hbL
  rw [ZMod.val_natCast, ZMod.val_natCast,
    Nat.mod_eq_of_lt haMod, Nat.mod_eq_of_lt hbMod] at hval
  exact hval

theorem isingTorusAxisSegment_card
    (i : Fin d) (r : Nat) (hr : r < isingDyadicSide k) :
    (isingTorusAxisSegment (k := k) i r).card = r + 1 := by
  unfold isingTorusAxisSegment
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro a ha b hb hab
    exact isingTorusCoordinateShift_injectiveOn_range i r hr
      (by simpa using ha) (by simpa using hb) hab


theorem finiteTorusBlockDifferenceAverage_zeroModeGreen_axisSegment
    (i : Fin d) (r : Nat) (hr : r < isingDyadicSide k) :
    finiteTorusBlockDifferenceAverage
        (finiteTorusZeroModeGreen
          (isingTorusCharacterDispersion (d := d) (k := k)))
        (isingTorusAxisSegment i r) =
      (1 / ((r + 1 : Nat) : Real) ^ 2) *
        ∑ a ∈ Finset.range (r + 1),
          ∑ b ∈ Finset.range (r + 1),
            isingDyadicTorusGreen
              (Pi.single i ((b : Int) - (a : Int))) k := by
  unfold finiteTorusBlockDifferenceAverage
  rw [isingTorusAxisSegment_card i r hr]
  apply congrArg ((1 / ((r + 1 : Nat) : Real) ^ 2) * ·)
  unfold isingTorusAxisSegment
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro b hb
      exact finiteTorusZeroModeGreen_axisDifference i a b
    · intro b hb c hc hbc
      exact isingTorusCoordinateShift_injectiveOn_range i r hr
        (by simpa using hb) (by simpa using hc) hbc
  · intro a ha b hb hab
    exact isingTorusCoordinateShift_injectiveOn_range i r hr
      (by simpa using ha) (by simpa using hb) hab

theorem isingTorusAxisSegment_nonempty (i : Fin d) (r : Nat) :
    (isingTorusAxisSegment (k := k) i r).Nonempty := by
  refine ⟨isingTorusCoordinateShift i 0, ?_⟩
  rw [isingTorusAxisSegment, Finset.mem_image]
  exact ⟨0, by simp, rfl⟩


end StatMech.FrontierA
