/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LongExactCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Homology.HomologySequence
import Theorem.v1.Atlas.AlgebraicGeometryI.code.LongExactCohomology


noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v u

namespace LongExactCohomology

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- The connecting homomorphism `H^n(C) → H^{n+1}(A)` in cohomology arising from
a short exact sequence of cochain complexes. -/
def connectingHomomorphism
    {S : CategoryTheory.ShortComplex (CochainComplex 𝒜 ℤ)}
    (hS : S.ShortExact) (n : ℤ) :
    S.X₃.homology n ⟶ S.X₁.homology (n + 1) :=
  hS.δ n (n + 1) (up_rel n)

end LongExactCohomology
end
