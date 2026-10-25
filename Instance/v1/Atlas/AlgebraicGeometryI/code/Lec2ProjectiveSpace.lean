/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec2ProjectiveSpace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Order
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Topology.Constructions
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec2ProjectiveSpace
set_option maxHeartbeats 800000

open scoped LinearAlgebra.Projectivization


noncomputable section

namespace Formalization

variable {k : Type*} [Field k] {n : ℕ}

/-- The Zariski topology on `A^{n+1}`, whose closed sets are the vanishing loci of sets of
polynomials. -/
instance zariskiTopologyAffine : TopologicalSpace (Fin (n + 1) → k) :=
  TopologicalSpace.ofClosed (Set.range (AffineSpace.zeroLocus k n))
    (⟨{1}, by ext x; simp [AffineSpace.zeroLocus]⟩)
    (by
      intro Zs hZs
      have hc : ∀ Z ∈ Zs, ∃ S, AffineSpace.zeroLocus k n S = Z :=
        fun Z hZ => let ⟨S, hS⟩ := hZs hZ; ⟨S, hS⟩
      classical
      choose S hS using hc
      use { p | ∃ Z, ∃ hZ : Z ∈ Zs, p ∈ S Z hZ }
      ext x
      constructor
      · intro hx
        apply mem_sInter.mpr
        intro Z hZ
        rw [← hS Z hZ]
        intro p hp
        exact hx p ⟨Z, hZ, hp⟩
      · intro hx p ⟨Z, hZ, hp⟩
        have hxZ := mem_sInter.mp hx Z hZ
        rw [← hS Z hZ] at hxZ
        exact hxZ p hp)
    (by
      rintro _ ⟨S, rfl⟩ _ ⟨T, rfl⟩
      refine ⟨AffineSpace.mulPairs k n S T, ?_⟩
      ext x
      simp only [AffineSpace.zeroLocus, AffineSpace.mulPairs, mem_setOf_eq, mem_union]
      constructor
      · intro hx
        by_contra hc
        push Not at hc
        obtain ⟨⟨f, hfS, hf⟩, ⟨g, hgT, hg⟩⟩ := hc
        exact absurd (show MvPolynomial.eval x (f * g) = 0 from hx _ ⟨f, hfS, g, hgT, rfl⟩)
          (by simp only [map_mul]; exact mul_ne_zero hf hg)
      · rintro (hS | hT) p ⟨f, hfS, g, hgT, rfl⟩
        · simp [map_mul, hS f hfS]
        · simp [map_mul, hT g hgT])

/-- The Zariski topology on `P^n`, defined as the quotient topology coinduced from the
Zariski topology on `A^{n+1}` via the projection `π`. -/
instance projectiveSpaceTopology : TopologicalSpace (ProjectiveSpace k n) :=
  TopologicalSpace.coinduced (Projectivization.mk' k) inferInstance

end Formalization
end
