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
import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part9
set_option autoImplicit false

open DifferentialFormSpace


/-- Pull the cutoff Gaussian data out of the Donaldson PDE-axioms instance. -/
noncomputable def cutoff_gaussian_data_exists'
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    [HasWeitzenbockDecomp Ω l2 dol]
    [hpde : HasDonaldsonPDEData Ω wdn l2 dol]
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) :
    CutoffGaussianData l2 dol fam := hpde.cutoffGaussianData fam

