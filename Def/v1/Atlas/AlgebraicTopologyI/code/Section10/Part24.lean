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
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section10.Part11
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


namespace BrouwerFixedPoint

open Metric Set Inner

variable {X : Type u} [TopologicalSpace X]

/-- The *antipodal map* `S^n → S^n`, `x ↦ -x`. Has degree `(-1)^{n+1}`. -/
def antipodalMap (n : ℕ) : sphereTopCat n ⟶ sphereTopCat n :=
  ⟨⟨fun x => ⟨-x.1, by
      have hx := x.2
      simp only [Metric.mem_sphere, dist_zero_right] at hx ⊢
      rw [norm_neg]; exact hx⟩,
    (continuous_neg.comp continuous_subtype_val).subtype_mk _⟩⟩

/-- The *coordinate reflection* `r_i : S^n → S^n` that negates the `i`-th coordinate and
fixes the others. Has degree `-1`. -/
def coordReflection (n : ℕ) (i : Fin (n + 1)) : sphereTopCat n ⟶ sphereTopCat n :=
  ⟨⟨fun x => ⟨(WithLp.equiv 2 _).symm
      (Function.update (WithLp.equiv 2 _ x.1) i (-(x.1 i))),
      update_neg_mem_sphere n i x⟩,
    (continuous_update_neg n i).comp continuous_subtype_val |>.subtype_mk _⟩⟩

/-- The composition of the first `k` coordinate reflections `r_{k-1} ∘ ... ∘ r_0`, a self-map
of `S^n`. Taking `k = n + 1` recovers the antipodal map (up to homotopy). -/
def iteratedReflection (n : ℕ) :
    (k : ℕ) → (hk : k ≤ n + 1) → (sphereTopCat n ⟶ sphereTopCat n)
  | 0, _ => 𝟙 _
  | k + 1, hk => coordReflection n ⟨k, by omega⟩ ≫ iteratedReflection n k (by omega)


end BrouwerFixedPoint
