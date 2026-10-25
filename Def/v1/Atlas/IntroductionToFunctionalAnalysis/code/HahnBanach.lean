/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/HahnBanach.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Order.Zorn


namespace HahnBanach

variable {K : Type*} {V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- A Hamel basis of a vector space $V$ over a field $K$ is a subset $H \subseteq V$ that is
linearly independent and whose $K$-linear span is all of $V$. Equivalently, every element of
$V$ can be written uniquely as a finite $K$-linear combination of elements of $H$. -/
def IsHamelBasis (K : Type*) {V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    (H : Set V) : Prop :=
  LinearIndependent K ((↑) : H → V) ∧ Submodule.span K H = ⊤

end HahnBanach
