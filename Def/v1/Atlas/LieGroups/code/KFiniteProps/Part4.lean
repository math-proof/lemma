/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.KFinite.Part3
import Lemma.Complex.IsKFinite0
import Lemma.Fin.Any_Eq_SMul.of.All_ToMonoidHom.IsIrreducible
import Lemma.Bijective.EqContinuousLinearEquivOfBijective.of.Bijective
import Def.v1.Atlas.LieGroups.code.SchurLemma
import Def.v1.Atlas.LieGroups.code.Admissible.Part3
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Theorem.v1.Atlas.LieGroups.code.KFiniteProps.Part3


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
