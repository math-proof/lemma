/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ClosedPointMorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.Divisors.Part11
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Divisors
open MulAction


namespace ClosedPoint

variable {G : Type*} [Group G]

variable {C₁ : Type*} {C₂ : Type*} [MulAction G C₁] [MulAction G C₂]

/-- A $G$-equivariant map $\varphi : C_1 \to C_2$ takes points in the same $G$-orbit to points in the same $G$-orbit. -/
lemma orbitRel_map_of_equivariant (φ : C₁ → C₂)
    (hφ : ∀ (g : G) (P : C₁), φ (g • P) = g • φ P)
    ⦃a b : C₁⦄ (hab : (orbitRel G C₁).r a b) :
    (orbitRel G C₂).r (φ a) (φ b) := by
  rw [orbitRel_apply] at hab ⊢
  obtain ⟨g, hg⟩ := hab
  exact ⟨g, by rw [← hg, hφ]⟩

end ClosedPoint
