/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCanonicalDenseIncidence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIncidence.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part17
import Def.StatisticalMechanics.Code.Universality.IsingFermionicCanonicalDenseIncidence.Part7
open Filter Set Topology


namespace StatMech.Universality

noncomputable section

theorem fkIsingExpandingSquareScale_mul_natAbs_floor_succ_le
    (c : Real) (k : Nat) :
    fkIsingExpandingSquareScale k *
        (⌊c * (k + 1 : Real)⌋ : Int).natAbs ≤ |c| + 1 := by
  let z : Int := ⌊c * (k + 1 : Real)⌋
  have hzUpper : (z : Real) ≤ c * (k + 1 : Real) := Int.floor_le _
  have hzLower : c * (k + 1 : Real) - 1 < (z : Real) :=
    Int.sub_one_lt_floor _
  have hzAbs : |(z : Real)| ≤ |c * (k + 1 : Real)| + 1 := by
    rw [abs_le]
    constructor <;>
      nlinarith [neg_abs_le (c * (k + 1 : Real)),
        le_abs_self (c * (k + 1 : Real))]
  have hspos : 0 < fkIsingExpandingSquareScale k :=
    fkIsingExpandingSquareScale_pos k
  have hscaleSucc :
      fkIsingExpandingSquareScale k * (k + 1 : Real) = 1 := by
    simp only [fkIsingExpandingSquareScale, one_div]
    push_cast
    exact inv_mul_cancel₀ (show (k : Real) + 1 ≠ 0 by positivity)
  have hsle : fkIsingExpandingSquareScale k ≤ 1 := by
    have ht : (1 : Real) ≤ k + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    nlinarith
  calc
    fkIsingExpandingSquareScale k * (z.natAbs : Real) =
        fkIsingExpandingSquareScale k * |(z : Real)| := by
          simp only [Nat.cast_natAbs, Int.cast_abs]
    _ ≤ fkIsingExpandingSquareScale k *
        (|c * (k + 1 : Real)| + 1) :=
      mul_le_mul_of_nonneg_left hzAbs hspos.le
    _ = |c| + fkIsingExpandingSquareScale k := by
      rw [mul_add, mul_one, abs_mul, abs_of_pos (by positivity :
        (0 : Real) < k + 1)]
      calc
        fkIsingExpandingSquareScale k * (|c| * (k + 1 : Real)) +
            fkIsingExpandingSquareScale k =
          |c| * (fkIsingExpandingSquareScale k * (k + 1 : Real)) +
            fkIsingExpandingSquareScale k := by ring
        _ = |c| + fkIsingExpandingSquareScale k := by rw [hscaleSucc, mul_one]
    _ ≤ |c| + 1 := by simpa [add_comm] using add_le_add_left hsle |c|


theorem fkIsingDenseRationalPath_length_le (q : Rat × Rat) (k : Nat) :
    (fkIsingDenseRationalPathSteps q k : Real) *
        (2 * fkIsingExpandingSquareScale k) ≤
      2 *
        (|((q.1 : Real) + (q.2 : Real)) / 2| +
          |((q.1 : Real) - (q.2 : Real)) / 2| + 2) := by
  let cx : Real := ((q.1 : Real) + (q.2 : Real)) / 2
  let cy : Real := ((q.1 : Real) - (q.2 : Real)) / 2
  have hxRaw :=
    fkIsingExpandingSquareScale_mul_natAbs_floor_succ_le cx k
  have hyRaw :=
    fkIsingExpandingSquareScale_mul_natAbs_floor_succ_le cy k
  have hx : fkIsingExpandingSquareScale k *
      (fkIsingDenseRationalPathX q k).natAbs ≤ |cx| + 1 := by
    by_cases h : FKIsingDenseRationalInterior q k
    · simpa [fkIsingDenseRationalPathX, h, fkIsingDenseRationalPrimalX,
        cx] using hxRaw
    · simp only [fkIsingDenseRationalPathX, h, if_false,
        Int.natAbs_zero, Nat.cast_zero, mul_zero]
      positivity
  have hy : fkIsingExpandingSquareScale k *
      (fkIsingDenseRationalPathY q k).natAbs ≤ |cy| + 1 := by
    by_cases h : FKIsingDenseRationalInterior q k
    · simpa [fkIsingDenseRationalPathY, h, fkIsingDenseRationalPrimalY,
        cy] using hyRaw
    · simp only [fkIsingDenseRationalPathY, h, if_false,
        Int.natAbs_zero, Nat.cast_zero, mul_zero]
      positivity
  dsimp [fkIsingDenseRationalPathSteps]
  push_cast
  dsimp [cx, cy] at hx hy ⊢
  nlinarith [fkIsingExpandingSquareScale_pos k]


end
end StatMech.Universality
