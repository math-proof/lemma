/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronDensity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEventualPerronBranch.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronDensity.Part2
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexPerronGaugeStage_le_eighthRoot (hc : 2 < c) (k : Nat) :
    sixVertexPerronGaugeStage hc k ≤
      Nat.sqrt (Nat.sqrt (Nat.sqrt (k + 1))) := by
  classical
  exact Nat.findGreatest_le _

theorem sixVertexPerronGaugeStage_le (hc : 2 < c) (k : Nat) :
    sixVertexPerronGaugeStage hc k ≤ k + 1 :=
  (sixVertexPerronGaugeStage_le_eighthRoot hc k).trans
    ((Nat.sqrt_le_self _).trans
      ((Nat.sqrt_le_self _).trans (Nat.sqrt_le_self _)))

theorem sixVertexPerronGaugeStage_pow_eight_le
    (hc : 2 < c) (k : Nat) :
    (sixVertexPerronGaugeStage hc k) ^ 8 ≤ k + 1 := by
  let a := sixVertexPerronGaugeStage hc k
  let b := Nat.sqrt (Nat.sqrt (k + 1))
  let d := k + 1
  have ha : a * a ≤ b := by
    calc
      a * a = a ^ 2 := by ring
      _ ≤ Nat.sqrt (Nat.sqrt (Nat.sqrt (k + 1))) ^ 2 := by
        dsimp [a]
        exact pow_le_pow_left₀ (Nat.zero_le _)
          (sixVertexPerronGaugeStage_le_eighthRoot hc k) 2
      _ = Nat.sqrt (Nat.sqrt (Nat.sqrt (k + 1))) *
          Nat.sqrt (Nat.sqrt (Nat.sqrt (k + 1))) := by ring
      _ ≤ b := by simpa [b] using Nat.sqrt_le (Nat.sqrt (Nat.sqrt (k + 1)))
  have hb : b * b ≤ Nat.sqrt (k + 1) := by
    simpa [b] using Nat.sqrt_le (Nat.sqrt (k + 1))
  have hd : Nat.sqrt (k + 1) * Nat.sqrt (k + 1) ≤ d := by
    simpa [d] using Nat.sqrt_le (k + 1)
  have ha4 : (a * a) * (a * a) ≤ b * b :=
    Nat.mul_le_mul ha ha
  have ha4' : a ^ 4 ≤ Nat.sqrt (k + 1) := by
    calc
      a ^ 4 = (a * a) * (a * a) := by ring
      _ ≤ b * b := ha4
      _ ≤ Nat.sqrt (k + 1) := hb
  calc
    a ^ 8 = a ^ 4 * a ^ 4 := by ring
    _ ≤ Nat.sqrt (k + 1) * Nat.sqrt (k + 1) :=
      Nat.mul_le_mul ha4' ha4'
    _ ≤ d := hd

theorem sixVertexPerronGaugeStage_threshold_le
    {c : Real} (hc : 2 < c) (k : Nat) :
    sixVertexPerronGaugeThreshold hc
        (sixVertexPerronGaugeStage hc k) ≤ k := by
  classical
  unfold sixVertexPerronGaugeStage
  exact Nat.findGreatest_spec
    (P := fun n => sixVertexPerronGaugeThreshold hc n ≤ k)
    (m := 0) (Nat.zero_le _) (by simp)

theorem tendsto_sixVertexPerronGaugeStage
    {c : Real} (hc : 2 < c) :
    Tendsto (sixVertexPerronGaugeStage hc) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro n
  refine ⟨max (n ^ 8) (sixVertexPerronGaugeThreshold hc n), ?_⟩
  intro k hk
  classical
  apply Nat.le_findGreatest
  · rw [Nat.le_sqrt, Nat.le_sqrt, Nat.le_sqrt]
    have hn : n ^ 8 ≤ k + 1 :=
      (le_max_left _ _).trans hk |>.trans (Nat.le_add_right _ _)
    calc
      n * n * (n * n) * (n * n * (n * n)) = n ^ 8 := by ring
      _ ≤ k + 1 := hn
  · exact (le_max_right _ _).trans hk


end
end StatMech.FrontierD
