/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ComplexProjectiveSpace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.AdvancedKahler
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ManifoldDFS
import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.ManifoldDFS

set_option autoImplicit false

open scoped Manifold ContDiff

noncomputable section

/-- The setoid on nonzero vectors in $\mathbb{C}^{n+1}$: $v \sim w$ iff $w = c v$ for some $c \in \mathbb{C}^\times$, used to define $\mathbb{CP}^n$. -/
def CPnSetoid (n : ℕ) : Setoid {v : Fin (n + 1) → ℂ // v ≠ 0} where
  r v w := ∃ (c : ℂ), c ≠ 0 ∧ (∀ i, w.1 i = c * v.1 i)
  iseqv :=
    ⟨fun v => ⟨1, one_ne_zero, fun i => by simp⟩,
     fun ⟨c, hc, h⟩ => ⟨c⁻¹, inv_ne_zero hc, fun i => by
        rw [h i, inv_mul_cancel_left₀ hc]⟩,
     fun ⟨c₁, hc₁, h₁⟩ ⟨c₂, hc₂, h₂⟩ => ⟨c₂ * c₁, mul_ne_zero hc₂ hc₁, fun i => by
        rw [h₂ i, h₁ i]; ring⟩⟩

/-- Complex projective space $\mathbb{CP}^n = (\mathbb{C}^{n+1} \setminus \{0\}) / \mathbb{C}^\times$. -/
def ComplexProjectiveSpace (n : ℕ) : Type :=
  Quotient (CPnSetoid n)

/-- $\mathbb{CP}^n$ carries the quotient topology from $\mathbb{C}^{n+1} \setminus \{0\}$. -/
instance CPn_topologicalSpace (n : ℕ) : TopologicalSpace (ComplexProjectiveSpace n) :=
  instTopologicalSpaceQuotient (s := CPnSetoid n)


/-- The smooth atlas on $\mathbb{CP}^n$ making it a $(2n)$-dimensional real charted space (via affine charts $U_i = \{[z_0 : \cdots : z_n] : z_i \ne 0\}$). -/
abbrev CPn_Ω (n : ℕ) : ℕ → Type :=
  ManifoldΩ (𝓡 (2 * n)) (ComplexProjectiveSpace n)

/-- Vector fields $\mathfrak{X}(\mathbb{CP}^n)$ in the DFS framework. -/
abbrev CPn_VF (n : ℕ) : Type :=
  ManifoldVF (𝓡 (2 * n)) (ComplexProjectiveSpace n)

/-- The differential-form-space structure on $\mathbb{CP}^n$. -/
noncomputable instance instCPnDFS (n : ℕ) :
    DifferentialFormSpace (CPn_Ω n) (CPn_VF n) :=
  manifoldDFS (𝓡 (2 * n)) (ComplexProjectiveSpace n)


/-- The Fubini–Study $2$-form $\omega_{\mathrm{FS}}$ on $\mathbb{CP}^n$: the canonical Kähler form, locally $\omega_{\mathrm{FS}} = \frac{i}{2} \partial \bar\partial \log(1 + |z|^2)$. -/
end
