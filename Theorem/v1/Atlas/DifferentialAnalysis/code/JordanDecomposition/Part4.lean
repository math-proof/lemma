/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/JordanDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.ContinuousFunctions.Part2
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.ContinuousFunctions
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
import Def.v1.Atlas.DifferentialAnalysis.code.JordanDecomposition.Part4


namespace ContinuousFunctions

open ContinuousLinearMap

section PosPartConstruction

variable {X : Type*} [MetricSpace X]

/-- Additivity of `posPartFn` on arbitrary `C₀` functions. -/
lemma posPartFn_add (u : C₀Map X →L[ℝ] ℝ) (f g : C₀Map X) :
    posPartFn u (f + g) = posPartFn u f + posPartFn u g := by
  unfold posPartFn

  have h_decomp : f + g = (zeroAtInftyPosPart f + zeroAtInftyPosPart g) -
      (zeroAtInftyNegPart f + zeroAtInftyNegPart g) := by
    conv_lhs => rw [decompose_pos_neg f, decompose_pos_neg g]
    ext x; simp only [ZeroAtInftyContinuousMap.coe_add, ZeroAtInftyContinuousMap.coe_sub,
      Pi.add_apply, Pi.sub_apply]; ring

  rw [posPartSup_well_defined u (f + g)
    (zeroAtInftyPosPart f + zeroAtInftyPosPart g)
    (zeroAtInftyNegPart f + zeroAtInftyNegPart g)
    (fun x => add_nonneg (posPart_nonneg f x) (posPart_nonneg g x))
    (fun x => add_nonneg (negPart_nonneg f x) (negPart_nonneg g x))
    h_decomp]
  rw [posPartSup_add u _ _ (posPart_nonneg f) (posPart_nonneg g)]
  rw [posPartSup_add u _ _ (negPart_nonneg f) (negPart_nonneg g)]
  ring

/-- Homogeneity of `posPartFn` under multiplication by a nonnegative scalar. -/
lemma posPartFn_smul_nonneg (u : C₀Map X →L[ℝ] ℝ) (f : C₀Map X) (c : ℝ) (hc : 0 ≤ c) :
    posPartFn u (c • f) = c * posPartFn u f := by
  unfold posPartFn

  have hpos : zeroAtInftyPosPart (c • f) = c • zeroAtInftyPosPart f := by
    ext x; simp only [posPart_apply, ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
    rcases le_or_gt (f x) 0 with h | h
    · rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos hc h)]
      rw [max_eq_right h]; ring
    · rw [max_eq_left (mul_nonneg hc h.le)]
      rw [max_eq_left h.le]
  have hneg : zeroAtInftyNegPart (c • f) = c • zeroAtInftyNegPart f := by
    ext x; simp only [negPart_apply, ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [show -(c * f x) = c * (-f x) by ring]
    rcases le_or_gt (-f x) 0 with h | h
    · rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos hc h)]
      rw [max_eq_right h]; ring
    · rw [max_eq_left (mul_nonneg hc h.le)]
      rw [max_eq_left h.le]
  rw [hpos, hneg]
  rw [posPartSup_smul_nonneg u _ (posPart_nonneg f) c hc]
  rw [posPartSup_smul_nonneg u _ (negPart_nonneg f) c hc]
  ring

/-- Homogeneity of `posPartFn` under multiplication by a negative scalar (using the symmetry
between positive and negative parts under negation). -/
lemma posPartFn_smul_neg (u : C₀Map X →L[ℝ] ℝ) (f : C₀Map X) (c : ℝ) (hc : c < 0) :
    posPartFn u (c • f) = c * posPartFn u f := by
  unfold posPartFn

  have hpos : zeroAtInftyPosPart (c • f) = (-c) • zeroAtInftyNegPart f := by
    ext x; simp only [posPart_apply, negPart_apply, ZeroAtInftyContinuousMap.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    rw [show c * f x = (-c) * (-f x) by ring]
    have hc' : 0 ≤ -c := neg_nonneg.mpr hc.le
    rcases le_or_gt (-f x) 0 with h | h
    · rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos hc' h)]
      rw [max_eq_right h]; ring
    · rw [max_eq_left (mul_nonneg hc' h.le)]
      rw [max_eq_left h.le]
  have hneg : zeroAtInftyNegPart (c • f) = (-c) • zeroAtInftyPosPart f := by
    ext x; simp only [negPart_apply, posPart_apply, ZeroAtInftyContinuousMap.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    rw [show -(c * f x) = (-c) * f x by ring]
    have hc' : 0 ≤ -c := neg_nonneg.mpr hc.le
    rcases le_or_gt (f x) 0 with h | h
    · rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos hc' h)]
      rw [max_eq_right h]; ring
    · rw [max_eq_left (mul_nonneg hc' h.le)]
      rw [max_eq_left h.le]
  rw [hpos, hneg]
  rw [posPartSup_smul_nonneg u _ (negPart_nonneg f) (-c) (neg_nonneg.mpr hc.le)]
  rw [posPartSup_smul_nonneg u _ (posPart_nonneg f) (-c) (neg_nonneg.mpr hc.le)]
  ring

/-- Full ℝ-linearity of `posPartFn` in the scalar argument. -/
lemma posPartFn_smul (u : C₀Map X →L[ℝ] ℝ) (f : C₀Map X) (c : ℝ) :
    posPartFn u (c • f) = c * posPartFn u f := by
  rcases le_or_gt 0 c with hc | hc
  · exact posPartFn_smul_nonneg u f c hc
  · exact posPartFn_smul_neg u f c hc

/-- Operator-norm bound for the positive part functional: `‖posPartFn u f‖ ≤ ‖u‖ * ‖f‖`. -/
lemma posPartFn_bound (u : C₀Map X →L[ℝ] ℝ) (f : C₀Map X) :
    ‖posPartFn u f‖ ≤ ‖u‖ * ‖f‖ := by
  unfold posPartFn
  rw [Real.norm_eq_abs]
  have h1 := posPartSup_le_norm_mul u (zeroAtInftyPosPart f) (posPart_nonneg f)
  have h2 := posPartSup_le_norm_mul u (zeroAtInftyNegPart f) (negPart_nonneg f)
  have h3 := posPartSup_nonneg u (zeroAtInftyPosPart f) (posPart_nonneg f)
  have h4 := posPartSup_nonneg u (zeroAtInftyNegPart f) (negPart_nonneg f)

  rw [abs_le]
  have hfp_le : ‖zeroAtInftyPosPart f‖ ≤ ‖f‖ := by
    change ‖(zeroAtInftyPosPart f).toBCF‖ ≤ ‖f.toBCF‖
    rw [BoundedContinuousFunction.norm_le (norm_nonneg f.toBCF)]
    intro x
    calc |zeroAtInftyPosPart f x| = zeroAtInftyPosPart f x :=
            abs_of_nonneg (posPart_nonneg f x)
      _ ≤ |f x| := posPart_le_abs f x
      _ ≤ ‖f‖ := c0_eval_le_norm f x
  have hfn_le : ‖zeroAtInftyNegPart f‖ ≤ ‖f‖ := by
    change ‖(zeroAtInftyNegPart f).toBCF‖ ≤ ‖f.toBCF‖
    rw [BoundedContinuousFunction.norm_le (norm_nonneg f.toBCF)]
    intro x
    calc |zeroAtInftyNegPart f x| = zeroAtInftyNegPart f x :=
            abs_of_nonneg (negPart_nonneg f x)
      _ ≤ |f x| := negPart_le_abs f x
      _ ≤ ‖f‖ := c0_eval_le_norm f x
  have h1' : posPartSup u (zeroAtInftyPosPart f) ≤ ‖u‖ * ‖f‖ :=
    le_trans h1 (mul_le_mul_of_nonneg_left hfp_le (norm_nonneg u))
  have h2' : posPartSup u (zeroAtInftyNegPart f) ≤ ‖u‖ * ‖f‖ :=
    le_trans h2 (mul_le_mul_of_nonneg_left hfn_le (norm_nonneg u))
  constructor <;> linarith

end PosPartConstruction
end ContinuousFunctions
