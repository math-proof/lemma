/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section5
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.LocalityPrinciple
import Def.v1.Atlas.AlgebraicTopologyI.code.Section5.Part6
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Def.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part5
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section10.Part10
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


namespace BrouwerFixedPoint

open Metric Set Inner

variable {X : Type u} [TopologicalSpace X]

/-- The (unreduced) **suspension** `Σf : S^{n+1} → S^{n+1}` of a self-map `f : S^n → S^n`,
obtained by restricting `suspRaw n f` to the unit sphere. -/
noncomputable def suspensionOfSphereMap (n : ℕ) (_hn : n ≥ 1)
    (f : sphereTopCat n ⟶ sphereTopCat n) :
    sphereTopCat (n + 1) ⟶ sphereTopCat (n + 1) :=
  ⟨⟨fun v => ⟨suspRaw n f v.val, by
      rw [Metric.mem_sphere, dist_zero_right]
      exact suspRaw_norm n f v.val
        (by have := v.property; rwa [Metric.mem_sphere, dist_zero_right] at this)⟩,
    Continuous.subtype_mk ((continuous_suspRaw n f).comp continuous_subtype_val) _⟩⟩

end BrouwerFixedPoint
