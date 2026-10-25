/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.Varieties.Part9
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Varieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Morphisms
import Def.v1.Atlas.ArithmeticGeometry.code.Morphisms.Part6
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Topology.NoetherianSpace
import Mathlib.RingTheory.MvPolynomial.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.ProductVarieties.Part4
variable (k : Type*) [Field k]


/-- Vanishing of the combined homogeneous polynomial set is invariant under rescaling each
of the two homogeneous coordinate vectors by a nonzero scalar (well-definedness on
projective coordinates). -/
lemma combinedHomogPolySet_vanish_of_rescale {k : Type*} [Field k] {m n : ℕ}
    {S_X : Set (HomogPoly k m)} {S_Y : Set (HomogPoly k n)}
    {a₁ : Fin (m + 1) → AlgebraicClosure k} {b₁ : Fin (n + 1) → AlgebraicClosure k}
    {a₂ : Fin (m + 1) → AlgebraicClosure k} {b₂ : Fin (n + 1) → AlgebraicClosure k}
    {c d : AlgebraicClosure k} (hc : c ≠ 0) (hd : d ≠ 0)
    (ha : a₁ = fun i => c * a₂ i) (hb : b₁ = fun i => d * b₂ i)
    (h : ∀ f ∈ combinedHomogPolySet m n S_X S_Y, eval (Fin.append a₁ b₁) f = 0) :
    ∀ f ∈ combinedHomogPolySet m n S_X S_Y, eval (Fin.append a₂ b₂) f = 0 := by
  intro f hf
  simp only [combinedHomogPolySet, Set.mem_union, embedHomogSetLeft, embedHomogSetRight,
    Set.mem_image] at hf
  rcases hf with ⟨p, ⟨g, hgS, rfl⟩, rfl⟩ | ⟨q, ⟨g, hgS, rfl⟩, rfl⟩
  · have hmem : (embedHomogPolyLeft m n) g.poly ∈ combinedHomogPolySet m n S_X S_Y :=
      Set.mem_union_left _ ⟨g.poly, ⟨g, hgS, rfl⟩, rfl⟩
    have heval := h _ hmem
    rw [eval_embedHomogPolyLeft] at heval ⊢
    rw [ha, homog_eval_rescale] at heval
    exact (mul_eq_zero.mp heval).resolve_left (pow_ne_zero _ hc)
  · have hmem : (embedHomogPolyRight m n) g.poly ∈ combinedHomogPolySet m n S_X S_Y :=
      Set.mem_union_right _ ⟨g.poly, ⟨g, hgS, rfl⟩, rfl⟩
    have heval := h _ hmem
    rw [eval_embedHomogPolyRight] at heval ⊢
    rw [hb, homog_eval_rescale] at heval
    exact (mul_eq_zero.mp heval).resolve_left (pow_ne_zero _ hd)

