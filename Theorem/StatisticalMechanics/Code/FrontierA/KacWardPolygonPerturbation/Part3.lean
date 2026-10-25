/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonPerturbation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardGenericPolygonReduction
import Def.StatisticalMechanics.Code.FrontierA.KacWardPolygonPerturbation.Part3


namespace StatMech.FrontierA

open scoped Convex

open Set

theorem denseRange_kwRatComplex : DenseRange kwRatComplex := by
  let realPair : ℚ × ℚ → ℝ × ℝ :=
    Prod.map ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ)
  let toComplex : ℝ × ℝ → ℂ := fun p ↦ p.1 + p.2 * Complex.I
  have hpair : DenseRange realPair :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have hsurj : Function.Surjective toComplex := by
    intro z
    refine ⟨(z.re, z.im), ?_⟩
    apply Complex.ext <;> simp [toComplex]
  have hcontinuous : Continuous toComplex := by
    unfold toComplex
    fun_prop
  have hcomp := hsurj.denseRange.comp hpair hcontinuous
  simpa only [Function.comp_def, realPair, toComplex, kwRatComplex,
    Prod.map_apply] using hcomp

end StatMech.FrontierA
