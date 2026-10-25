/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part11
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.AdvancedKahler
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.HodgeTheory
import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part12
import Mathlib.Geometry.Manifold.MFDeriv.Basic
set_option autoImplicit false

open DifferentialFormSpace


/-- A tangent-bundle splitting compatible with a 2-form $\eta$.

Encodes a decomposition $TM = V \oplus H$ into vertical and horizontal subbundles via
projections `projV` and `projH`. Contraction with $\eta$ (and with any $(p+1)$-form)
distributes over the splitting, the projections are idempotent and mutually
annihilating, and the splitting is "orthogonal" with respect to $\eta$ in the sense
that $\iota_{V Y} \iota_{H X} \eta = 0$. -/
class TangentSplitting
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (η : Ω 2) where
  projV : VF → VF
  projH : VF → VF
  decompose : ∀ (X : VF) {p : ℕ} (α : Ω (p + 1)),
    inst.ι X α = inst.ι (projV X) α + inst.ι (projH X) α
  projV_idem : ∀ (X : VF), projV (projV X) = projV X
  projH_idem : ∀ (X : VF), projH (projH X) = projH X
  complement_VH : ∀ (X : VF) {p : ℕ} (α : Ω (p + 1)),
    inst.ι (projV (projH X)) α = 0
  complement_HV : ∀ (X : VF) {p : ℕ} (α : Ω (p + 1)),
    inst.ι (projH (projV X)) α = 0
  orthogonal : ∀ (X Y : VF),
    inst.ι (projV Y) (inst.ι (projH X) η) = 0


