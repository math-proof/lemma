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
import Theorem.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part4
set_option autoImplicit false

open DifferentialFormSpace


/-- Donaldson's PDE-axiom package: provides cutoff Gaussian data for every
section family, Cauchy estimates for every Green operator, holomorphicity of
the corrected $k=0$ section, and the $L^2$ zero-edge correction bound. -/
class HasDonaldsonPDEData
    (Ω : ℕ → Type*) {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    [HasWeitzenbockDecomp Ω l2 dol] where
  cutoffGaussianData : ∀ (fam : ApproxHolomorphicSectionFamily (inst := inst)),
    CutoffGaussianData l2 dol fam
  cauchyEstimates : ∀ (greenOp : HasGreenOperator Ω l2 dol),
    ∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧
      ∀ (k : ℕ) (s : Ω 0),
        wdn.weighted_supnorm k r (greenOp.greenCorrection k s) ≤
          C_r * l2.l2norm (greenOp.greenCorrection k s)
  correctionHolAtZero : ∀ (fam : ApproxHolomorphicSectionFamily (inst := inst)) (p : VF),
    dol.delbar (fam.section_ 0 p +
      (HasWeitzenbockDecomp.toHasGreenOperator l2 dol).greenCorrection 0 (fam.section_ 0 p)) = 0
  correctionL2ZeroEdge : ∀ (fam : ApproxHolomorphicSectionFamily (inst := inst))
    (c_G : ℝ) (C_g : ℝ) (lam : ℝ),
    C_g > 0 → lam > 0 →
    (∀ (k : ℕ) (p : VF),
      l2.l2norm (dol.delbar (fam.section_ k p)) ≤
        C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3))) →
    ∀ (p : VF),
      l2.l2norm ((HasWeitzenbockDecomp.toHasGreenOperator l2 dol).greenCorrection 0 (fam.section_ 0 p)) ≤
        Real.sqrt c_G * C_g * Real.exp (-lam * (0 : ℝ) ^ ((1 : ℝ) / 3))

