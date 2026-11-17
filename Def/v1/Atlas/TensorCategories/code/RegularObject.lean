/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/RegularObject.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Abbrev.v1.Atlas.TensorCategories.code.RegularObject

@[expose] public section

namespace FormalProjectiveSum

variable {I : Type*}

/-- The coefficient of basis element `i` in the formal sum `s`. -/
def coeff (s : FormalProjectiveSum I) (i : I) : ℝ := s i

/-- The standard basis element of `FormalProjectiveSum I` associated to `i`,
namely the indicator function supported at `i` with value `1`. -/
noncomputable def basis (i : I) : FormalProjectiveSum I :=
  Finsupp.single i 1

/-- The Frobenius–Perron dimension of a formal projective sum `s`, given the
Frobenius–Perron dimensions `fpDimP` of the basis projectives. -/
noncomputable def fpdim [Fintype I] (s : FormalProjectiveSum I) (fpDimP : I → ℝ) : ℝ :=
  ∑ i : I, s.coeff i * fpDimP i

/-- Promote a function `I → ℝ` on a finite type to a `FormalProjectiveSum I`. -/
noncomputable def ofFun [Fintype I] (f : I → ℝ) : FormalProjectiveSum I :=
  Finsupp.equivFunOnFinite.symm f

end FormalProjectiveSum
