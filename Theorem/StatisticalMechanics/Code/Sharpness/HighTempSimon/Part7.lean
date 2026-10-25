/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSwitching.Part4
import Def.StatisticalMechanics.Code.Sharpness.HighTempSimon.Part9
open Finset SimpleGraph
open scoped BigOperators symmDiff


namespace StatMech

namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp] theorem twoPointJ_self (beta : ℝ) (J : Sym2 V → ℝ) (a : V) :
    twoPointJ G beta J a a = 1 := by
  rw [twoPointJ, sourcePair_self]
  unfold expectationJ partitionJ
  simp only [spinProd_empty, one_mul]
  exact div_self (ne_of_gt (partitionJ_pos G beta J))


theorem twoPointJ_high_temp_ratio (beta : ℝ) (J : Sym2 V → ℝ)
    (a b : V) :
    twoPointJ G beta J a b =
      highTempSourceSum G.edgeFinset
          (fun e => Real.tanh (beta * J e)) (sourcePair a b) /
        highTempSourceSum G.edgeFinset
          (fun e => Real.tanh (beta * J e)) ∅ := by
  unfold twoPointJ
  rw [expectationJ_high_temp_ratio]
  unfold highTempSourceSum highTempSourceSubgraphs
  simp only [highTempSubgraphWeight]
  apply congrArg₂ (· / ·)
  · rfl
  · apply Finset.sum_congr
    · ext F
      simp only [Finset.mem_filter, hasOddBoundary_empty]
    · intro F _
      rfl


theorem highTempSourceSum_empty_pos (E : Finset (Sym2 V))
    (t : Sym2 V → ℝ) (ht : ∀ e ∈ E, 0 ≤ t e) :
    0 < highTempSourceSum E t ∅ := by
  unfold highTempSourceSum highTempSourceSubgraphs
  have hempty : (∅ : Finset (Sym2 V)) ∈
      E.powerset.filter (fun F => HasOddBoundary F ∅) := by
    rw [Finset.mem_filter, Finset.mem_powerset, hasOddBoundary_empty]
    exact ⟨Finset.empty_subset _, by
      intro v
      simp [incCount]⟩
  calc
    0 < (1 : ℝ) := zero_lt_one
    _ = ∏ e ∈ (∅ : Finset (Sym2 V)), t e := by simp
    _ ≤ ∑ F ∈ E.powerset.filter (fun F => HasOddBoundary F ∅),
          ∏ e ∈ F, t e := by
      rw [← Finset.add_sum_erase _ _ hempty]
      simp only [Finset.prod_empty]
      exact le_add_of_nonneg_right (Finset.sum_nonneg (fun F hF =>
        Finset.prod_nonneg (fun e he => by
          have hmem := Finset.mem_of_mem_erase hF
          have hpow := (Finset.mem_filter.mp hmem).1
          exact ht e ((Finset.mem_powerset.mp hpow) he))))


theorem twoPointJ_couplingIn_high_temp_ratio (beta : ℝ)
    (J : Sym2 V → ℝ) (S : Finset V) (a b : V) :
    twoPointJ G beta (couplingIn J S) a b =
      highTempSourceSum (highTempInternalEdges G S)
          (fun e => Real.tanh (beta * J e)) (sourcePair a b) /
        highTempSourceSum (highTempInternalEdges G S)
          (fun e => Real.tanh (beta * J e)) ∅ := by
  rw [twoPointJ_high_temp_ratio]
  rw [highTempSourceSum_couplingIn G beta J S (sourcePair a b),
    highTempSourceSum_couplingIn G beta J S ∅]


theorem twoPointJ_simon_finite (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (S : Finset V) (o z : V) (ho : o ∈ S) (hz : z ∉ S) :
    twoPointJ G beta J o z ≤
      ∑ x ∈ S, ∑ y ∈ (Finset.univ \ S),
        Real.tanh (beta * J s(x, y)) *
          twoPointJ G beta (couplingIn J S) o x *
          twoPointJ G beta J y z := by
  let t : Sym2 V → ℝ := fun e => Real.tanh (beta * J e)
  have ht : ∀ e, 0 ≤ t e := by
    intro e
    change 0 ≤ Real.tanh (beta * J e)
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg
      (Real.sinh_nonneg_iff.mpr (mul_nonneg hbeta (hJ e)))
      (Real.cosh_pos _).le
  let ZG := highTempSourceSum G.edgeFinset t ∅
  let ZS := highTempSourceSum (highTempInternalEdges G S) t ∅
  let N := highTempSourceSum G.edgeFinset t (sourcePair o z)
  let R := ∑ x ∈ S, ∑ y ∈ (Finset.univ \ S),
    t s(x, y) *
      (highTempSourceSum (highTempInternalEdges G S) t (sourcePair o x) / ZS) *
      highTempSourceSum G.edgeFinset t (sourcePair y z)
  have hZG : 0 < ZG := highTempSourceSum_empty_pos G.edgeFinset t
    (fun e _ => ht e)
  have hZS : 0 < ZS := highTempSourceSum_empty_pos
    (highTempInternalEdges G S) t (fun e _ => ht e)
  have hcross : N * ZS ≤
      ∑ x ∈ S, ∑ y ∈ (Finset.univ \ S),
        t s(x, y) *
          highTempSourceSum (highTempInternalEdges G S) t (sourcePair o x) *
          highTempSourceSum G.edgeFinset t (sourcePair y z) := by
    exact highTemp_sourceSum_simon G t ht S o z ho hz
  have hNR : N ≤ R := by
    apply le_of_mul_le_mul_right _ hZS
    calc
      N * ZS ≤ ∑ x ∈ S, ∑ y ∈ (Finset.univ \ S),
          t s(x, y) *
            highTempSourceSum (highTempInternalEdges G S) t (sourcePair o x) *
            highTempSourceSum G.edgeFinset t (sourcePair y z) := hcross
      _ = R * ZS := by
        unfold R
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro y _
        field_simp
  have hrat : N / ZG ≤ R / ZG :=
    div_le_div_of_nonneg_right hNR hZG.le
  rw [twoPointJ_high_temp_ratio G beta J o z,
    show highTempSourceSum G.edgeFinset
      (fun e => Real.tanh (beta * J e)) (sourcePair o z) = N by rfl,
    show highTempSourceSum G.edgeFinset
      (fun e => Real.tanh (beta * J e)) ∅ = ZG by rfl]
  calc
    N / ZG ≤ R / ZG := hrat
    _ = ∑ x ∈ S, ∑ y ∈ (Finset.univ \ S),
        Real.tanh (beta * J s(x, y)) *
          twoPointJ G beta (couplingIn J S) o x *
          twoPointJ G beta J y z := by
      unfold R
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro y _
      rw [twoPointJ_couplingIn_high_temp_ratio,
        twoPointJ_high_temp_ratio]
      dsimp only [t, ZS, ZG]
      ring


theorem twoPointJ_nonneg (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (a b : V) :
    0 ≤ twoPointJ G beta J a b := by
  let t : Sym2 V → ℝ := fun e => Real.tanh (beta * J e)
  have ht : ∀ e, 0 ≤ t e := by
    intro e
    change 0 ≤ Real.tanh (beta * J e)
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg
      (Real.sinh_nonneg_iff.mpr (mul_nonneg hbeta (hJ e)))
      (Real.cosh_pos _).le
  rw [twoPointJ_high_temp_ratio]
  exact div_nonneg
    (Finset.sum_nonneg (fun F _ => Finset.prod_nonneg (fun e _ => ht e)))
    (highTempSourceSum_empty_pos G.edgeFinset t (fun e _ => ht e)).le


end Sharpness
end StatMech
