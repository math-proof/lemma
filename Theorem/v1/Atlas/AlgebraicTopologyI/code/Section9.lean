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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section9
open CategoryTheory


namespace HomologyLongExactSequence

variable {C ι : Type*} [Category C] [Abelian C] {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex C c)}

/-- Exactness of the long exact sequence at the middle term `Hᵢ(B)`: the image of
`Hᵢ(A) → Hᵢ(B)` equals the kernel of `Hᵢ(B) → Hᵢ(C)` for a short exact sequence of
chain complexes. -/
theorem exact_f_g (hS : S.ShortExact) (i : ι) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap S.f i)
      (HomologicalComplex.homologyMap S.g i) (by
        rw [← HomologicalComplex.homologyMap_comp, S.zero,
          HomologicalComplex.homologyMap_zero])).Exact :=
  ShortComplex.ShortExact.homology_exact₂ hS i

/-- Exactness of the long exact sequence at `Hᵢ(C)`: the image of `Hᵢ(B) → Hᵢ(C)` equals
the kernel of the connecting map `∂ : Hᵢ(C) → Hⱼ(A)`. -/
theorem exact_g_δ (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    (ShortComplex.mk _ _ (ShortComplex.ShortExact.comp_δ hS i j hij)).Exact :=
  ShortComplex.ShortExact.homology_exact₃ hS i j hij

/-- Exactness of the long exact sequence at `Hⱼ(A)`: the image of the connecting map
`∂ : Hᵢ(C) → Hⱼ(A)` equals the kernel of `Hⱼ(A) → Hⱼ(B)`. -/
theorem exact_δ_f (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    (ShortComplex.mk _ _ (ShortComplex.ShortExact.δ_comp hS i j hij)).Exact :=
  ShortComplex.ShortExact.homology_exact₁ hS i j hij

end HomologyLongExactSequence
