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
import Def.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part6
set_option autoImplicit false

open DifferentialFormSpace


/-- Reflexivity: `fam.L` is the same as `correction_bundle_data_axiom fam`. -/
theorem correction_bundle_eq_axiom
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) :
    fam.L = correction_bundle_data_axiom fam := rfl

/-- Edge case bound: at $k = 0$ the $L^2$-norm of the Green correction is
controlled by $\sqrt{c_G}\, C_g\, e^{-\lambda \cdot 0^{1/3}}$, used to
initialize the inductive Donaldson construction. -/
theorem correction_l2_zero_edge_axiom
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (_wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    [HasWeitzenbockDecomp Ω l2 dol]
    [hpde : HasDonaldsonPDEData Ω _wdn l2 dol]
    (fam : ApproxHolomorphicSectionFamily (inst := inst))
    (c_G : ℝ) (C_g : ℝ) (lam : ℝ)
    (_hCg_pos : C_g > 0) (_hlam_pos : lam > 0)
    (_h_gauss : ∀ (k : ℕ) (p : VF),
      l2.l2norm (dol.delbar (fam.section_ k p)) ≤
        C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3))) :
    ∀ (p : VF),
      l2.l2norm ((weitzenbock_green_operator_axiom l2 dol).greenCorrection 0 (fam.section_ 0 p)) ≤
        Real.sqrt c_G * C_g * Real.exp (-lam * (0 : ℝ) ^ ((1 : ℝ) / 3)) :=
  hpde.correctionL2ZeroEdge fam c_G C_g lam _hCg_pos _hlam_pos _h_gauss

