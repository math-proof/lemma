/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveMorphisms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties.Part7
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.ProjectiveVarieties
import Mathlib.Algebra.MvPolynomial.Monad


noncomputable section

open MvPolynomial

open scoped LinearAlgebra.Projectivization

namespace ProjectiveRegularFunction

variable {n : ℕ} (k : Type*) [Field k]

/-- A homogeneous representative of a projective regular function: a pair of homogeneous polynomials $(\text{num}, \text{den})$ of the same degree on $\mathbb{P}^n$, with $\text{den} \neq 0$, representing the rational function $\text{num}/\text{den}$. -/
structure HomogeneousRep (n : ℕ) (k : Type*) [Field k] where
  num : MvPolynomial (Fin (n + 1)) k
  den : MvPolynomial (Fin (n + 1)) k
  deg : ℕ
  num_homog : num.IsHomogeneous deg
  den_homog : den.IsHomogeneous deg
  den_ne_zero : den ≠ 0

end ProjectiveRegularFunction
end
