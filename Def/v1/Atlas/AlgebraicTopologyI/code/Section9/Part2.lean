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
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section9
open CategoryTheory


namespace HomologyLongExactSequence

variable {C ι : Type*} [Category C] [Abelian C] {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex C c)}

/-- **Theorem 9.1** (Homology long exact sequence). Given a short exact sequence
`0 → A → B → C → 0` of chain complexes, there is a natural connecting homomorphism
`∂ : Hₙ(C) → Hₙ₋₁(A)` such that
`⋯ → Hₙ(A) → Hₙ(B) → Hₙ(C) →∂ Hₙ₋₁(A) → ⋯`
is exact. This bundles the connecting map together with exactness at each spot. -/
noncomputable def homologyLongExactSequence
    (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    HomologyLongExactSequenceData hS i j hij where
  δ := connectingHomomorphism hS i j hij
  exact_at_X₂ := exact_f_g hS i
  exact_at_X₃ := exact_g_δ hS i j hij
  exact_at_X₁ := exact_δ_f hS i j hij

end HomologyLongExactSequence
