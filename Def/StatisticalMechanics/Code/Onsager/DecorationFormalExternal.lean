/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalExternal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalSurgery.Part2


namespace StatMech.Onsager

open BigOperators Finset

noncomputable def ons_decFormalRootedLogCoeff
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) : ℂ :=
  -(∑ r ∈ Finset.range (ons_finsuppTotalDegree m),
    ons_decFormalFixedBucketE L a b d r m / ((r : ℂ) + 1))

noncomputable def ons_decFormalAvoidLogCoeff
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) : ℂ :=
  -(∑ r ∈ Finset.range (ons_finsuppTotalDegree m),
    ons_decFormalFixedBucketN L a b d r m / ((r : ℂ) + 1)) / 2

noncomputable def ons_decFormalRootedLog
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L) :
    MvPowerSeries (ons_DecEdge L) ℂ :=
  ons_decFormalRootedLogCoeff L a b d

noncomputable def ons_decFormalAvoidLog
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L) :
    MvPowerSeries (ons_DecEdge L) ℂ :=
  ons_decFormalAvoidLogCoeff L a b d

end StatMech.Onsager
