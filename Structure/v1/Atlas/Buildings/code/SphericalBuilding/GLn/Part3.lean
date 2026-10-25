/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Order.RelClasses
import Mathlib.Data.Matrix.Basic
import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLn.Part2


namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)

/-- An apartment associated to the frame $F$: a flag every member of which is compatible
with $F$. -/
structure Apartment (F : Frame k n) where
  flag : SubspaceFlag k n
  compatible : ∀ V ∈ flag.chain, F.IsCompatible k n V

/-- The building axioms for the flag complex of $\mathrm{GL}_n(k)$: (i) every panel extends to
two distinct chambers (thinness), (ii) any two flags lie in a common apartment, and
(iii) two apartments sharing two chambers admit a compatibility-preserving isomorphism
fixing both chambers. -/
structure IsBuilding where
  apartment_thin : ∀ (F : Frame k n) (panel : SubspaceFlag k n),
    (∀ V ∈ panel.chain, F.IsCompatible k n V) →
    panel.chain.length = n - 2 →
    ∃ C₁ C₂ : SubspaceFlag k n,
      IsChamber k n C₁ ∧ IsChamber k n C₂ ∧ C₁ ≠ C₂ ∧
      (∀ V ∈ panel.chain, V ∈ C₁.chain) ∧
      (∀ V ∈ panel.chain, V ∈ C₂.chain) ∧
      (∀ V ∈ panel.chain, V ∈ C₁.chain ∧ V ∈ C₂.chain)
  common_apartment : ∀ (σ τ : SubspaceFlag k n),
    ∃ F : Frame k n, (∀ V ∈ σ.chain, F.IsCompatible k n V) ∧
                      (∀ V ∈ τ.chain, F.IsCompatible k n V)
  apartment_iso : ∀ (F₁ F₂ : Frame k n) (C₁ C₂ : SubspaceFlag k n),
    IsChamber k n C₁ → IsChamber k n C₂ →
    (∀ V ∈ C₁.chain, F₁.IsCompatible k n V) →
    (∀ V ∈ C₂.chain, F₁.IsCompatible k n V) →
    (∀ V ∈ C₁.chain, F₂.IsCompatible k n V) →
    (∀ V ∈ C₂.chain, F₂.IsCompatible k n V) →
    ∃ f : Submodule k (Vec k n) → Submodule k (Vec k n),
      Function.Bijective f ∧
      (∀ V, F₁.IsCompatible k n V → F₂.IsCompatible k n (f V)) ∧
      (∀ V ∈ C₁.chain, f V = V) ∧
      (∀ V ∈ C₂.chain, f V = V)

/-- Data of a $BN$-pair for $\mathrm{GL}_n(k)$: a standard chamber, standard frame, and the
subgroups $B$ and $N$ (encoded as sets of matrices). -/
structure GLnBNPairData where
  stdFlag : SubspaceFlag k n
  stdFlag_chamber : IsChamber k n stdFlag
  stdFrame : Frame k n
  B : Set (Matrix (Fin n) (Fin n) k)
  N : Set (Matrix (Fin n) (Fin n) k)

end GLnBuilding
