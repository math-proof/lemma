/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Order.KrullDimension
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Def.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties

public section

noncomputable section

open MvPolynomial Finsupp

namespace HomogeneousPolynomial

variable {σ : Type*} {R : Type*} [CommSemiring R]

/-- Homogeneity under scaling: if $f$ is homogeneous of degree $d$, then
$f(c x_1, \ldots, c x_n) = c^d \cdot f(x_1, \ldots, x_n)$ for every scalar
$c$. -/
theorem isHomogeneous_eval_smul (f : MvPolynomial σ R) (d : ℕ) (hf : f.IsHomogeneous d)
    (c : R) (x : σ → R) :
    eval (fun i => c * x i) f = c ^ d * eval x f := by
  rw [f.as_sum, map_sum, map_sum, Finset.mul_sum]
  congr 1
  ext s
  simp only [eval_monomial]
  by_cases hs : coeff s f = 0
  · simp [hs]
  · have hdeg : s.degree = d := by
      rw [degree_eq_weight_one]; exact hf hs
    simp only [prod]
    simp_rw [mul_pow]
    rw [Finset.prod_mul_distrib]
    rw [← hdeg, degree_apply, ← Finset.prod_pow_eq_pow_sum]
    ring

end HomogeneousPolynomial
end
