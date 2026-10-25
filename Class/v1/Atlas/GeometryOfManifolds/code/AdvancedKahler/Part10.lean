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
import Def.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part7
set_option autoImplicit false

open DifferentialFormSpace


/-- Bundles all data needed to run Donaldson's Proposition 1 proof on a compact
symplectic manifold with compatible almost-complex structure: a weighted
sup-norm, an $L^2$-norm, a Dolbeault operator, Gaussian peak sections, a
Weitzenböck decomposition, and the PDE-axioms package. -/
class HasDonaldsonProofData
    (Ω : ℕ → Type*) {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (S : SymplecticManifold Ω VF) (J : AlmostComplexStr (inst := inst))
    (hcompat : IsCompatibleACS S J) where
  wdn : WeightedDerivSupNorm Ω (inst := inst)
  l2 : L2NormSpace Ω (inst := inst)
  dol : DolbeaultOps (inst := inst)
  gaussianPeakInst : HasGaussianPeakData Ω S J hcompat
  weitzenbockInst : HasWeitzenbockDecomp Ω l2 dol
  pdeDataInst : @HasDonaldsonPDEData Ω VF inst _ wdn l2 dol weitzenbockInst

