/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierEvaluation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheBulkReduction.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFreeEnergyReduction
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierEvaluation.Part3
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem one_add_tanh_mul_exp_neg_two_sub_one (x : Real) :
    (1 + Real.tanh x) * (Real.exp (-2 * x) - 1) =
      -2 * Real.tanh x := by
  let a := Real.exp x
  let b := Real.exp (-x)
  have hab : a * b = 1 := by
    dsimp [a, b]
    rw [← Real.exp_add]
    simp
  have hab' : b * a = 1 := by rw [mul_comm, hab]
  have hsum : a + b ≠ 0 := by
    dsimp [a, b]
    positivity
  rw [Real.tanh_eq]
  rw [show Real.exp (-2 * x) = b * b by
    dsimp [b]
    rw [← Real.exp_add]
    congr 1
    ring]
  change (1 + (a - b) / (a + b)) * (b * b - 1) =
    -2 * ((a - b) / (a + b))
  field_simp [hsum]
  have habb : a * b ^ 2 = b := by
    rw [pow_two, ← mul_assoc, hab, one_mul]
  nlinarith [habb]


theorem sixVertexOffsetFourierPartialSum_eq_gapPartialSum
    (lam : Real) (N : Nat) :
    sixVertexOffsetFourierPartialSum lam N =
      lam + 2 * ∑ n ∈ range N, sixVertexGapSeriesTerm lam n := by
  unfold sixVertexOffsetFourierPartialSum
  let f : Nat → Real := fun n =>
    (-1 : Real) ^ (n + 1) *
      (Real.exp (-2 * (n + 1 : Real) * lam) - 1) / (n + 1 : Real)
  let g : Nat → Real := fun n =>
    (-1 : Real) ^ (n + 1) * Real.tanh ((n + 1 : Real) * lam) *
      (Real.exp (-2 * (n + 1 : Real) * lam) - 1) / (n + 1 : Real)
  change lam - (∑ n ∈ range N, f n) - (∑ n ∈ range N, g n) = _
  have hcombine :
      lam - (∑ n ∈ range N, f n) - (∑ n ∈ range N, g n) =
        lam + ∑ n ∈ range N, (-f n - g n) := by
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    ring
  rw [hcombine, Finset.mul_sum]
  apply congrArg (fun t : Real => lam + t)
  apply Finset.sum_congr rfl
  intro n hn
  let x : Real := (n + 1 : Real) * lam
  let a : Real := (-1 : Real) ^ (n + 1) / (n + 1 : Real)
  have hcore := one_add_tanh_mul_exp_neg_two_sub_one x
  dsimp [f, g]
  have hf :
      (-1 : Real) ^ (n + 1) *
          (Real.exp (-2 * (n + 1 : Real) * lam) - 1) / (n + 1 : Real) =
        a * (Real.exp (-2 * x) - 1) := by
    dsimp [a, x]
    ring
  have hg :
      (-1 : Real) ^ (n + 1) * Real.tanh ((n + 1 : Real) * lam) *
          (Real.exp (-2 * (n + 1 : Real) * lam) - 1) / (n + 1 : Real) =
        a * Real.tanh x * (Real.exp (-2 * x) - 1) := by
    dsimp [a, x]
    ring
  rw [hf, hg]
  have hleft :
      -(a * (Real.exp (-2 * x) - 1)) -
          a * Real.tanh x * (Real.exp (-2 * x) - 1) =
        -a * ((1 + Real.tanh x) * (Real.exp (-2 * x) - 1)) := by
    ring
  rw [hleft, hcore]
  unfold sixVertexGapSeriesTerm
  dsimp [a, x]
  ring


theorem sixVertexOffsetFourierPartialSum_tendsto
    {lam : Real} (hlam : 0 < lam) :
    Tendsto (sixVertexOffsetFourierPartialSum lam) atTop
      (nhds (sixVertexAntiferroelectricGapRate lam)) := by
  have hsum := sixVertexGapSeries_partialSum_tendsto hlam
  have hconst : Tendsto (fun _ : Nat => lam) atTop (nhds lam) :=
    tendsto_const_nhds
  have hlim := hconst.add (hsum.const_mul 2)
  apply hlim.congr'
  filter_upwards [] with N
  exact (sixVertexOffsetFourierPartialSum_eq_gapPartialSum lam N).symm


end
end StatMech.FrontierD
