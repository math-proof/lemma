module
public import Def.v1.Atlas.LieGroups.code.KFinite.Part3
public import Theorem.Complex.IsKFinite0
public import Theorem.Fin.Any_Eq_SMul.of.All_ToMonoidHom.IsIrreducible
public import Theorem.LinearMap.EqContinuousLinearEquivOfBijective.of.Bijective
public import Def.v1.Atlas.LieGroups.code.SchurLemma
public import Def.v1.Atlas.LieGroups.code.Admissible.Part3
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Theorem.v1.Atlas.LieGroups.code.KFiniteProps.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open scoped ComplexOrder

universe uG uM

namespace MonoidAlgebra

/-- Dot-notation alias used by Lemma wrappers: `μ.sum f` = `μ.coeff.sum f`. -/
def sum {k G : Type*} [Semiring k] [Monoid G]
    (μ : MonoidAlgebra k G) (f : G → k → ℝ) : ℝ :=
  μ.coeff.sum f

end MonoidAlgebra
end
