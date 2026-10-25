/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LongExactSequence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma


noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v u

namespace LongExactSequence

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type*} {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex C c)}


/-- The connecting homomorphism `H_i(C) → H_j(A)` of the long exact homology
sequence arising from a short exact sequence of complexes. -/
def cohomologyδ (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    S.X₃.homology i ⟶ S.X₁.homology j :=
  hS.δ i j hij

end LongExactSequence
end
