/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/FourierAffinePlane.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.ProjectionTheory.code.FourierFF
import Lemma.Real.Atlas.v1.ProjectionTheory.code.FourierFF

open Finset hiding card
open Fintype (card)
open scoped BigOperators Classical

attribute [local instance] Fintype.ofFinite

namespace FourierFF

variable {p : ℕ} [Fact (Nat.Prime p)] {d : ℕ}

/-- The annihilator (orthogonal complement) of a subspace `V ⊂ 𝔽_p^d` with respect
to the standard dot product: `V^⊥ = {ξ : ⟨ξ, v⟩ = 0 for all v ∈ V}`. -/
def dotProdAnnihilator (V : Submodule (ZMod p) (Fin d → ZMod p)) :
    Set (Fin d → ZMod p) :=
  {ξ | ∀ v : Fin d → ZMod p, v ∈ V → dotProd ξ v = 0}

/-- The characteristic function of the affine subspace `a + V ⊂ 𝔽_p^d`: it equals
`1` on the coset `{a + v : v ∈ V}` and `0` elsewhere. -/
noncomputable def cosetIndicator (V : Submodule (ZMod p) (Fin d → ZMod p))
    (a : Fin d → ZMod p) : (Fin d → ZMod p) → ℂ :=
  fun x => if x - a ∈ V then 1 else 0
