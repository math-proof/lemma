/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM1/PDEClassification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Inductive.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM1.PDEClassification
open Matrix Finset


namespace PDEClassification

variable {N : Type*} [Fintype N] [DecidableEq N]

section Classification

variable {A : Matrix N N ℝ} (hA : A.IsHermitian)

/-- $A$ is elliptic iff all eigenvalues of $A$ are strictly positive, or all are strictly
negative — i.e. the leading-symbol matrix is definite. -/
def IsElliptic : Prop :=
  (∀ i, 0 < hA.eigenvalues i) ∨ (∀ i, hA.eigenvalues i < 0)

/-- $A$ is hyperbolic iff all eigenvalues are nonzero and there exists an index $j$ such
that every other eigenvalue has sign opposite to that of $\lambda_j$ (signature
$(1, n-1)$ or $(n-1, 1)$). -/
def IsHyperbolic : Prop :=
  (∀ i, hA.eigenvalues i ≠ 0) ∧
  (∃ j, ∀ i, i ≠ j → hA.eigenvalues i * hA.eigenvalues j < 0)

/-- $A$ is parabolic iff there is exactly one zero eigenvalue (at some index $j$) and all
other eigenvalues are nonzero and share a common sign (their pairwise products are
positive). -/
def IsParabolic : Prop :=
  ∃ j, hA.eigenvalues j = 0 ∧
    (∀ i, i ≠ j → hA.eigenvalues i ≠ 0) ∧
    (∀ i₁ i₂, i₁ ≠ j → i₂ ≠ j → 0 < hA.eigenvalues i₁ * hA.eigenvalues i₂)

end Classification
end PDEClassification
