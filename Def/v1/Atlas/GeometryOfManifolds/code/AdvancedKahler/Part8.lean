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
import Theorem.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part7
set_option autoImplicit false

open DifferentialFormSpace


/-- Convert a `GreenCorrectionPDEAxioms` package into the `GreenCorrectionInput`
structure used by `correctedFamily` and the holomorphic-correction theorems. -/
noncomputable def GreenCorrectionInput_of_pde_axioms
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    (fam : ApproxHolomorphicSectionFamily (inst := inst))
    (pde : GreenCorrectionPDEAxioms wdn l2 dol fam) :
    GreenCorrectionInput wdn l2 dol fam where
  greenOp :=
    { greenCorrection := pde.greenCorrection,
      green_holomorphic := pde.green_holomorphic,
      green_l2_sq_bound := fun k hk s => by

        obtain ⟨C, hC_pos, h_unif⟩ := pde.uniform_spectral_gap
        exact ⟨C, hC_pos, h_unif k hk s⟩ }
  gaussian_decay := pde.gaussian_decay
  cauchy_estimates := pde.cauchy_estimates
  correction_l2_exp_bound :=
    correction_l2_exp_bound_from_spectral_gap wdn l2 dol fam pde
  hol_at_zero := pde.hol_at_zero
  same_bundle_data := pde.same_bundle_data
  corrected_bundle_eq := pde.corrected_bundle_eq

/-- Construct the Donaldson Green-correction PDE-axiom package on a compact
Kähler manifold by combining the Weitzenböck decomposition with the Donaldson
PDE-data infrastructure. -/
noncomputable def donaldson_green_correction_pde_axioms
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF) (J : AlmostComplexStr (inst := inst))
    (_hK : IsKahler S J) (_hcompat : IsCompatibleACS S J)
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    [wb : HasWeitzenbockDecomp Ω l2 dol]
    [hpde : HasDonaldsonPDEData Ω wdn l2 dol]
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) :
    GreenCorrectionPDEAxioms wdn l2 dol fam where
  greenCorrection := wb.greenCorrection
  green_holomorphic := wb.green_holomorphic
  uniform_spectral_gap := ⟨wb.c_G, wb.c_G_pos, wb.uniform_l2_bound⟩
  gaussian_decay := gaussian_decay_delbar_axiom wdn l2 dol fam
  cauchy_estimates := cauchy_estimates_axiom wdn l2 dol
  hol_at_zero := hpde.correctionHolAtZero fam
  same_bundle_data := fam.L
  corrected_bundle_eq := rfl
  correction_l2_at_zero := by
    obtain ⟨C_g, lam, hCg, hlam, hbound⟩ := gaussian_decay_delbar_axiom wdn l2 dol fam
    have h0 := hpde.correctionL2ZeroEdge fam wb.c_G C_g lam hCg hlam hbound
    exact ⟨Real.sqrt wb.c_G * C_g * Real.exp (-lam * (0 : ℝ) ^ ((1 : ℝ) / 3)),
           mul_pos (mul_pos (Real.sqrt_pos.mpr wb.c_G_pos) hCg) (Real.exp_pos _), h0⟩

/-- Existence of a `GreenCorrectionInput` on a compact Kähler manifold equipped
with the Weitzenböck decomposition and Donaldson PDE data: obtained by
composing `donaldson_green_correction_pde_axioms` with
`GreenCorrectionInput_of_pde_axioms`. -/
noncomputable def donaldson_green_correction_exists
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF) (J : AlmostComplexStr (inst := inst))
    (_hK : IsKahler S J) (_hcompat : IsCompatibleACS S J)
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    [HasWeitzenbockDecomp Ω l2 dol]
    [HasDonaldsonPDEData Ω wdn l2 dol]
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) :
    GreenCorrectionInput wdn l2 dol fam :=
  GreenCorrectionInput_of_pde_axioms wdn l2 dol fam
    (donaldson_green_correction_pde_axioms S J _hK _hcompat wdn l2 dol fam)


