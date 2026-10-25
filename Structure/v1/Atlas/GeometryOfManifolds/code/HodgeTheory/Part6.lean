/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Theorem.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part2
set_option autoImplicit false

open DifferentialFormSpace


/-- The Lefschetz operator $L: \Omega^p \to \Omega^{p+2}$, $\alpha \mapsto \omega \wedge \alpha$
on a symplectic manifold; it commutes with $d$. -/
structure LefschetzOp
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF) where
  L_op : ∀ {p : ℕ}, Ω p → Ω (p + 2)
  d_commutes : ∀ {p : ℕ} (α : Ω p), L_op (inst.d α) = inst.d (L_op α)

/-- The dual Lefschetz operator $\Lambda = L^*: \Omega^{p+2} \to \Omega^p$, the formal
$L^2$-adjoint of $L$. -/
structure DualLefschetz
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF] where
  Λ_op : ∀ {p : ℕ}, Ω (p + 2) → Ω p


/-- An action of the almost-complex structure $J$ on differential forms:
an $\mathbb{R}$-linear involution-up-to-sign $J: \Omega^p \to \Omega^p$ with $J^2 = -\mathrm{id}$. -/
structure JActsOnForms
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (J : AlmostComplexStr (inst := inst)) where
  J_form : ∀ {p : ℕ}, Ω p → Ω p
  J_form_sq : ∀ {p : ℕ} (α : Ω p), J_form (J_form α) = -(α)
  J_form_add : ∀ {p : ℕ} (α β : Ω p), J_form (α + β) = J_form α + J_form β
  J_form_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω p), J_form (r • α) = r • J_form α


