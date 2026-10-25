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
import Theorem.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part6
set_option autoImplicit false

open DifferentialFormSpace


/-- Assemble the full `GreenCorrectionInput` for a family using the Weitzenböck
decomposition, the cutoff Gaussian decay, Cauchy estimates, and the $k=0$
zero-edge bound provided by the Donaldson PDE axioms. -/
noncomputable def green_correction_data_sorry
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    [HasWeitzenbockDecomp Ω l2 dol]
    [HasDonaldsonPDEData Ω wdn l2 dol]
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) :
    GreenCorrectionInput wdn l2 dol fam :=


  buildGreenCorrectionInput wdn l2 dol fam

    (weitzenbock_green_operator_axiom l2 dol)

    (weitzenbock_uniform_constant_axiom l2 dol)
    (weitzenbock_uniform_constant_pos l2 dol)
    (weitzenbock_uniform_l2_bound_axiom l2 dol)

    (gaussian_decay_delbar_axiom wdn l2 dol fam)

    (cauchy_estimates_axiom wdn l2 dol)

    (correction_hol_at_zero_axiom wdn l2 dol fam)

    (correction_bundle_data_axiom fam)
    (correction_bundle_eq_axiom fam)

    (fun C_g lam hCg hlam h_gauss =>
      correction_l2_zero_edge_axiom wdn l2 dol fam
        (weitzenbock_uniform_constant_axiom l2 dol) C_g lam hCg hlam h_gauss)

