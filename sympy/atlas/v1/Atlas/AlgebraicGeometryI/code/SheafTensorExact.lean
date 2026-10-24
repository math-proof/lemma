/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafTensorExact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.Localization
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace SheafTensorExact

/-- **Locally free** module of rank `n`: there is a finite set `S ⊆ R` generating
the unit ideal such that for each `f ∈ S`, the localization `M[f⁻¹]` is a free
`R[f⁻¹]`-module of rank `n`. This is the algebraic version of "locally free
sheaf trivializes on the principal open cover `{D(f) : f ∈ S}`". -/
def IsLocallyFree (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    (n : ℕ) : Prop :=
  ∃ (S : Finset R), Ideal.span (S : Set R) = ⊤ ∧
    ∀ f ∈ S, Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) ∧
      Module.finrank (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) = n
