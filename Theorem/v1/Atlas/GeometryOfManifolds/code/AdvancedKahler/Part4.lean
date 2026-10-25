/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ConnectionsCurvature
import Structure.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature.Part7
import Structure.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part9
set_option autoImplicit false

open DifferentialFormSpace


/-- Convert a `CutoffGaussianData` polynomial-times-exponential bound into a
pure exponential bound: $\|\bar\partial s_{k,p}\|_{L^2} \le C_g\, e^{-\lambda k^{1/3}}$. -/
theorem derive_gaussian_l2_bound'
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    {l2 : L2NormSpace Ω (inst := inst)}
    {dol : DolbeaultOps (inst := inst)}
    {fam : ApproxHolomorphicSectionFamily (inst := inst)}
    (cgd : CutoffGaussianData l2 dol fam) :
    ∃ (C_g : ℝ) (lam : ℝ), C_g > 0 ∧ lam > 0 ∧
      ∀ (k : ℕ) (p : VF),
        l2.l2norm (dol.delbar (fam.section_ k p)) ≤
          C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3)) := by
  obtain ⟨C_g, lam, hCg, hlam, h_absorb⟩ :=
    absorb_poly_into_exp cgd.A_sup cgd.lam_0 cgd.A_sup_pos cgd.lam_0_pos
  refine ⟨C_g, lam, hCg, hlam, ?_⟩
  intro k p
  set t := (k : ℝ) ^ ((1 : ℝ) / 3) with ht_def
  have ht_nn : 0 ≤ t := Real.rpow_nonneg (Nat.cast_nonneg k) _
  calc l2.l2norm (dol.delbar (fam.section_ k p))
      ≤ cgd.A_sup * t * Real.exp (-cgd.lam_0 * t) := cgd.l2_delbar_bound k p
    _ ≤ C_g * Real.exp (-lam * t) := h_absorb t ht_nn

