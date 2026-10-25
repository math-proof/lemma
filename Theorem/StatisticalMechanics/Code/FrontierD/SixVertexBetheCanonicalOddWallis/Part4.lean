/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallis.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddLogUnregularization
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.NumberTheory.Harmonic.Bounds
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallis.Part4


namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

theorem sixVertexOddWallisReferenceLogSum_eq_log (m : Nat) :
    sixVertexOddWallisReferenceLogSum m =
      Real.log (sixVertexOddWallisHalfProduct m) := by
  unfold sixVertexOddWallisReferenceLogSum sixVertexOddWallisHalfProduct
  rw [Real.log_prod]
  intro j hj
  simp only [Finset.mem_range] at hj
  positivity

theorem tendsto_sixVertexOddWallisReferenceLog (s : Nat) :
    Tendsto (fun k =>
      Real.log (sixVertexFourWidth (2 * s + 1) k : Real) +
        2 * sixVertexOddWallisReferenceLogSum (s + k + 1))
      atTop (nhds (Real.log (4 / Real.pi))) := by
  have hproduct := (tendsto_sixVertexOddWallisReferenceProduct s).log
    (by positivity : (4 / Real.pi : Real) ≠ 0)
  apply hproduct.congr'
  filter_upwards [] with k
  let N := sixVertexFourWidth (2 * s + 1) k
  let m := s + k + 1
  have hN : (N : Real) ≠ 0 := by
    exact_mod_cast (sixVertexFourWidth_pos (2 * s + 1) k).ne'
  have hP : sixVertexOddWallisHalfProduct m ≠ 0 := by
    unfold sixVertexOddWallisHalfProduct
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    simp only [Finset.mem_range] at hj
    positivity
  rw [sixVertexOddWallisReferenceLogSum_eq_log]
  rw [Real.log_mul hN (pow_ne_zero 2 hP), Real.log_pow]
  rfl

theorem tendsto_sixVertexCanonicalOddCountingWallisLog
    {c : Real} (hc : 2 < c) (s : Nat) :
    Tendsto (fun k =>
      let N := sixVertexFourWidth (2 * s + 1) k
      let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
      let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
      Real.log (N : Real) +
        2 * ∑ j : Fin (s + k + 1),
          (Real.log (sixVertexBetheCountingFunction c N n p
              (sixVertexCanonicalOddLeftHalfRoot hc s k j)) -
            Real.log (sixVertexBetheCountingFunction c N n p
              (sixVertexCanonicalOddMidpointHalfRoot hc s k j))))
      atTop (nhds (Real.log (4 / Real.pi))) := by
  let E : Nat -> Real := fun k =>
    let N := sixVertexFourWidth (2 * s + 1) k
    let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
    let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
    ∑ j : Fin (s + k + 1),
      (Real.log (sixVertexBetheCountingFunction c N n p
          (sixVertexCanonicalOddMidpointHalfRoot hc s k j)) -
        Real.log (((j : Real) + 1) / N))
  have hE : Tendsto E atTop (nhds 0) := by
    exact tendsto_sum_log_sixVertexCanonicalOddMidpointCounting_sub_reference
      hc s
  have href := tendsto_sixVertexOddWallisReferenceLog s
  have hcomb := href.sub (hE.const_mul 2)
  have hcomb' : Tendsto (fun k =>
      Real.log (sixVertexFourWidth (2 * s + 1) k : Real) +
        2 * sixVertexOddWallisReferenceLogSum (s + k + 1) -
          2 * E k) atTop (nhds (Real.log (4 / Real.pi))) := by
    simpa using hcomb
  apply hcomb'.congr'
  filter_upwards [] with k
  let N := sixVertexFourWidth (2 * s + 1) k
  let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
  let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
  have hN : 0 < (N : Real) := by
    exact_mod_cast sixVertexFourWidth_pos (2 * s + 1) k
  have hNne : (sixVertexFourWidth (2 * s + 1) k : Real) ≠ 0 := by
    exact_mod_cast (sixVertexFourWidth_pos (2 * s + 1) k).ne'
  have hterm (j : Fin (s + k + 1)) :
      Real.log (sixVertexBetheCountingFunction c N n p
          (sixVertexCanonicalOddLeftHalfRoot hc s k j)) -
        Real.log (((j : Real) + 1) / N) =
      Real.log (((2 * j.val + 1 : Nat) : Real) / (2 * j.val + 2)) := by
    rw [sixVertexCanonicalOddLeftHalfRoot_countingFunction hc s k j]
    dsimp [N]
    rw [← Real.log_div]
    · congr 1
      field_simp [hN.ne']
      push_cast
      simp [hNne, mul_assoc]
      ring
    · positivity
    · positivity
  have hreference :
      (∑ j : Fin (s + k + 1),
        (Real.log (sixVertexBetheCountingFunction c N n p
            (sixVertexCanonicalOddLeftHalfRoot hc s k j)) -
          Real.log (((j : Real) + 1) / N))) =
        sixVertexOddWallisReferenceLogSum (s + k + 1) := by
    calc
      _ = ∑ j : Fin (s + k + 1),
          Real.log (((2 * j.val + 1 : Nat) : Real) /
            (2 * j.val + 2)) := by
        apply Finset.sum_congr rfl
        intro j _
        exact hterm j
      _ = ∑ j ∈ Finset.range (s + k + 1),
          Real.log (((2 * j + 1 : Nat) : Real) / (2 * j + 2)) := by
        simpa using (Fin.sum_univ_eq_sum_range (fun j : Nat =>
          Real.log (((2 * j + 1 : Nat) : Real) / (2 * j + 2)))
            (s + k + 1))
      _ = _ := rfl
  dsimp [E]
  rw [← hreference]
  simp only [Finset.sum_sub_distrib]
  ring

end
end StatMech.FrontierD
