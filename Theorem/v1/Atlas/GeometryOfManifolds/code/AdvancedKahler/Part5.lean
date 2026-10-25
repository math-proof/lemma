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
import Def.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part5
set_option autoImplicit false

open DifferentialFormSpace


/-- Cauchy estimates for the Green correction of any Green operator, taken
from the Donaldson PDE axioms. -/
theorem cauchy_estimates_for_green_op'
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    [HasWeitzenbockDecomp Ω l2 dol]
    [hpde : HasDonaldsonPDEData Ω wdn l2 dol]
    (greenOp : HasGreenOperator Ω l2 dol) :
    ∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧
      ∀ (k : ℕ) (s : Ω 0),
        wdn.weighted_supnorm k r (greenOp.greenCorrection k s) ≤
          C_r * l2.l2norm (greenOp.greenCorrection k s) := hpde.cauchyEstimates greenOp

/-- Exponential ($k^{1/3}$) Gaussian decay of $\bar\partial$ on any
section family, derived from the cutoff Gaussian data via absorption. -/
theorem gaussian_decay_delbar_axiom
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    [HasWeitzenbockDecomp Ω l2 dol]
    [HasDonaldsonPDEData Ω wdn l2 dol]
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) :
    ∃ (C_g : ℝ) (lam : ℝ), C_g > 0 ∧ lam > 0 ∧
      ∀ (k : ℕ) (p : VF),
        l2.l2norm (dol.delbar (fam.section_ k p)) ≤
          C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3)) :=
  derive_gaussian_l2_bound' (cutoff_gaussian_data_exists' wdn l2 dol fam)

/-- Cauchy estimates specialized to the Weitzenböck-derived Green operator. -/
theorem cauchy_estimates_axiom
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    [HasWeitzenbockDecomp Ω l2 dol]
    [HasDonaldsonPDEData Ω wdn l2 dol] :
    ∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧
      ∀ (k : ℕ) (s : Ω 0),
        wdn.weighted_supnorm k r ((weitzenbock_green_operator_axiom l2 dol).greenCorrection k s) ≤
          C_r * l2.l2norm ((weitzenbock_green_operator_axiom l2 dol).greenCorrection k s) :=
  cauchy_estimates_for_green_op' wdn l2 dol (weitzenbock_green_operator_axiom l2 dol)

/-- The corrected section at $k = 0$ is holomorphic:
$\bar\partial(s_{0,p} + G(s_{0,p})) = 0$. -/
theorem correction_hol_at_zero_axiom
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (_wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    [HasWeitzenbockDecomp Ω l2 dol]
    [hpde : HasDonaldsonPDEData Ω _wdn l2 dol]
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) :
    ∀ (p : VF),
      dol.delbar (fam.section_ 0 p +
        (weitzenbock_green_operator_axiom l2 dol).greenCorrection 0 (fam.section_ 0 p)) = 0 :=
  hpde.correctionHolAtZero fam

