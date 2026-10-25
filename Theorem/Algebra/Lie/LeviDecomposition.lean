/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.BilinearForm
/-!
# Levi decomposition

This file proves Weyl's complete reducibility theorem and the Levi decomposition for
finite-dimensional Lie algebras over fields of characteristic zero.
-/


namespace LeviDecomposition

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

theorem levi_sum_repr
    {K V ι : Type*} [Semiring K] [AddCommMonoid V] [Module K V]
    [Fintype ι] (b : Module.Basis ι K V) (x : V) :
    ∑ i, b.repr x i • b i = x := by
  apply b.repr.injective
  ext j
  simp

theorem levi_repr_eq_dual
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Finite ι] [DecidableEq ι] {B : LinearMap.BilinForm K V}
    (hB : B.Nondegenerate) (b : Module.Basis ι K V) (x : V) (i : ι) :
    b.repr x i = B (B.dualBasis hB b i) x := by
  let _ := Fintype.ofFinite ι
  conv_rhs => rw [← levi_sum_repr b x]
  rw [map_sum]
  simp_rw [map_smul]
  simp_rw [LinearMap.BilinForm.apply_dualBasis_left hB b]
  simp

end LeviDecomposition
