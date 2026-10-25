/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section9.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.Homology.HomologySequence
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section9
open CategoryTheory


namespace HomologyLongExactSequence

variable {C ι : Type*} [Category C] [Abelian C] {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex C c)}

/-- Packaged data for the homology long exact sequence (Theorem 9.1): the connecting
homomorphism `δ` and the three exactness statements (at `Hᵢ(B)`, at `Hᵢ(C)`, and at
`Hⱼ(A)`) for a short exact sequence of chain complexes. -/
structure HomologyLongExactSequenceData (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) where
  δ : S.X₃.homology i ⟶ S.X₁.homology j
  exact_at_X₂ : (ShortComplex.mk
      (HomologicalComplex.homologyMap S.f i)
      (HomologicalComplex.homologyMap S.g i) (by
        rw [← HomologicalComplex.homologyMap_comp, S.zero,
          HomologicalComplex.homologyMap_zero])).Exact
  exact_at_X₃ : (ShortComplex.mk _ _ (ShortComplex.ShortExact.comp_δ hS i j hij)).Exact
  exact_at_X₁ : (ShortComplex.mk _ _ (ShortComplex.ShortExact.δ_comp hS i j hij)).Exact

end HomologyLongExactSequence
