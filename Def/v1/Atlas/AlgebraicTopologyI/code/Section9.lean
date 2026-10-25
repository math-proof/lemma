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
open CategoryTheory


namespace HomologyLongExactSequence

variable {C ι : Type*} [Category C] [Abelian C] {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex C c)}

/-- The connecting (boundary) homomorphism `∂ : Hᵢ(C) ⟶ Hⱼ(A)` associated with a short exact
sequence `0 → A → B → C → 0` of chain complexes, where `j` is the index reached from `i`
under the complex shape. This is the key map appearing in the homology long exact sequence
(Theorem 9.1). -/
noncomputable def connectingHomomorphism
    (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    S.X₃.homology i ⟶ S.X₁.homology j :=
  ShortComplex.ShortExact.δ hS i j hij

end HomologyLongExactSequence
