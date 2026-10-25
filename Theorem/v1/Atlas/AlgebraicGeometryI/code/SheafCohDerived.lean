/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohDerived.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.EffaceableUniversal
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.EffaceableUniversal
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SheafCohomology
import Theorem.v1.Atlas.AlgebraicGeometryI.code.SheafCohomology.Part2
import Def.v1.Atlas.AlgebraicGeometryI.code.SheafCohDerived


noncomputable section

open CohomologyP1 SheafCohomology CategoryTheory CategoryTheory.Limits

namespace SheafCohDerived

section EulerDerived

variable (k : Type) [Field k]

/-- Derived version of Serre duality on `ℙ¹`: `dim H¹(O(n)) = dim H⁰(O(-2 - n))`. -/
theorem serre_duality_derived (n : ℤ) :
    Module.finrank k (H1 k n) = Module.finrank k (H0 k (-2 - n)) := by
  by_cases hn : 0 ≤ n
  · exact serre_duality_nonneg k n hn
  · push Not at hn; exact serre_duality_neg k n hn

end EulerDerived


section Bridge

variable (k : Type) [Field k]

/-- Effaceability witness: for every `n`, there exists `N ≥ max 0 n` with
`H¹(O(N)) = 0`. -/
theorem cech_effaceability_witness (n : ℤ) :
    ∃ N : ℤ, 0 ≤ N ∧ n ≤ N ∧ Module.finrank k (H1 k N) = 0 := by
  refine ⟨max 0 n, le_max_left 0 n, le_max_right 0 n, ?_⟩
  exact finrank_H1_of_nonneg k (max 0 n) (le_max_left 0 n)

end Bridge
end SheafCohDerived
end
