/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalanceContraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarRemoval.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
import Def.StatisticalMechanics.Code.Lattice.BalanceContraction
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem balancePreservingContraction_of_rep (h : BalancePreservingContractionRep) :
    BalancePreservingContraction := by
  intro K hK hge a
  obtain ⟨n, K', hK', hne', a', hlt, hbal⟩ := h K hK hge a
  refine ⟨K', hK', hne', a', hlt, ?_⟩
  rw [hbal, cornerBalance_iterate_dartNextSub K hK a n]


theorem balancePreservingContractionRep_iff :
    BalancePreservingContractionRep ↔ BalancePreservingContraction := by
  constructor
  · exact balancePreservingContraction_of_rep
  · intro h K hK hge a
    obtain ⟨K', hK', hne', a', hlt, hbal⟩ := h K hK hge a
    exact ⟨0, K', hK', hne', a', hlt, by rw [Function.iterate_zero_apply]; exact hbal⟩


theorem unitCell_cornerBalance_dartNextSub :
    cornerBalance unitCell (dartNextSub unitCell ucBase) = cornerBalance unitCell ucBase :=
  cornerBalance_dartNextSub unitCell unitCell_finite ucBase


theorem domino_cornerBalance_dartNextSub :
    cornerBalance domino (dartNextSub domino dmBase) = cornerBalance domino dmBase :=
  cornerBalance_dartNextSub domino domino_finite dmBase


end Lattice
end StatMech
