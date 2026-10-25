/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopSourceRootedDerivative.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopAddedEdgeRooted
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopHighTempResummation.Part7
open scoped BigOperators
open Filter SimpleGraph


namespace StatMech.Onsager

open StatMech.FrontierA

noncomputable section

theorem derivative_eq_source_of_eventually_sq_eq_sq
    (root : Complex -> Complex) (base source rootDeriv : Complex)
    (hroot : HasDerivAt root rootDeriv 0)
    (hzero : root 0 = base) (hbase : base ≠ 0)
    (hsq : (fun t => root t ^ 2) =ᶠ[nhds 0]
      (fun t => (base + t * source) ^ 2)) :
    rootDeriv = source := by
  let affine : Complex -> Complex := fun t => base + t * source
  have haffine : HasDerivAt affine source 0 := by
    dsimp only [affine]
    convert (hasDerivAt_const (x := (0 : Complex)) base).add
      ((hasDerivAt_id (x := (0 : Complex))).mul_const source) using 1
    all_goals ring
  have hsq' : (fun t => root t * root t) =ᶠ[nhds 0]
      (fun t => affine t * affine t) := by
    filter_upwards [hsq] with t ht
    simpa [pow_two, affine] using ht
  have hderiv := ((hroot.mul hroot).congr_of_eventuallyEq hsq'.symm).unique
    (haffine.mul haffine)
  dsimp only [affine] at hderiv
  rw [hzero] at hderiv
  have htwo : (2 : Complex) * base ≠ 0 :=
    mul_ne_zero (by norm_num) hbase
  apply mul_left_cancel₀ htwo
  linear_combination hderiv

end
end StatMech.Onsager
