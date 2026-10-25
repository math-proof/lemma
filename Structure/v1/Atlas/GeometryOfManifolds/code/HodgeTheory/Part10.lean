/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part9
set_option autoImplicit false

open DifferentialFormSpace


/-- A Green-operator decomposition $\mathrm{id} = LG + H$ where $H$ is the harmonic
projection (with $LH = 0$) and $G$ is the Green operator (inverse of $L$ on
$(\ker L)^\perp$). Asserts the orthogonality $\langle H\alpha, LG\alpha\rangle = 0$. -/
structure HasGreenOperatorDecomp
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (L : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)) where
  G : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)
  H : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)
  H_maps_to_ker : ∀ {p : ℕ} (α : Ω (p + 1)), L (H α) = 0
  LG_eq : ∀ {p : ℕ} (α : Ω (p + 1)), L (G α) = α + -(H α)
  GL_eq : ∀ {p : ℕ} (α : Ω (p + 1)), G (L α) = α + -(H α)
  H_idem : ∀ {p : ℕ} (α : Ω (p + 1)), H (H α) = H α
  G_add : ∀ {p : ℕ} (α β : Ω (p + 1)), G (α + β) = G α + G β
  H_add : ∀ {p : ℕ} (α β : Ω (p + 1)), H (α + β) = H α + H β
  G_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω (p + 1)), G (r • α) = r • G α
  H_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω (p + 1)), H (r • α) = r • H α
  G_preserves_regularity : ∀ [sob : HasSobolevSpaces Ω VF] (s : ℕ) {p : ℕ} (α : Ω (p + 1)),
    sob.IsSobolevRegular s α → sob.IsSobolevRegular s (G α)
  H_preserves_regularity : ∀ [sob : HasSobolevSpaces Ω VF] (s : ℕ) {p : ℕ} (α : Ω (p + 1)),
    sob.IsSobolevRegular s α → sob.IsSobolevRegular s (H α)
  orth_decomp : ∀ (cod : Codifferential (inst := inst))
      (ip : @L2InnerProduct Ω VF inst cod)
      {p : ℕ} (α : Ω (p + 1)),
      ip.inner (H α) (L (G α)) = 0
  G_H_eq_zero : ∀ {p : ℕ} (α : Ω (p + 1)), G (H α) = 0
  H_G_eq_zero : ∀ {p : ℕ} (α : Ω (p + 1)), H (G α) = 0


/-- The formal adjoint $\bar\partial^*: \Omega^{p+1} \to \Omega^p$ of the Dolbeault
operator $\bar\partial$. -/
structure DelbarStar
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (dol : DolbeaultOps (inst := inst)) where
  delbar_star : ∀ {p : ℕ}, Ω (p + 1) → Ω p
  delbar_star_add : ∀ {p : ℕ} (α β : Ω (p + 1)),
    delbar_star (α + β) = delbar_star α + delbar_star β
  delbar_star_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω (p + 1)),
    delbar_star (r • α) = r • delbar_star α

/-- The formal adjoint $\partial^*: \Omega^{p+1} \to \Omega^p$ of the Dolbeault
operator $\partial$. -/
structure DelStar
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (dol : DolbeaultOps (inst := inst)) where
  del_star : ∀ {p : ℕ}, Ω (p + 1) → Ω p
  del_star_add : ∀ {p : ℕ} (α β : Ω (p + 1)),
    del_star (α + β) = del_star α + del_star β
  del_star_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω (p + 1)),
    del_star (r • α) = r • del_star α


