/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.BoxCrossing.Part3
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.BXPAllAspect
import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.PlanarMengerDualityClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.MengerBarrierClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.CoastlineContinuityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.CoastlineAnchorClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.CircuitReachClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.BoxArcConnectsClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.RCoastMengerClose.Part2
import Def.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part2
open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped NNReal
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem crr_hasInterfaceSide_of_with (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {f q : Site 2}
    (h : crr_InterfaceSideWith ω n f q) : crr_HasInterfaceSide ω n f := by
  obtain ⟨hqR, pL, hpL, hadj, hpLbox, hqbox, hpLc, hqc⟩ := h
  exact ⟨pL, q, hpL, hqR, hadj, hpLbox, hqbox, hpLc, hqc⟩


theorem crr_rCoastFace_interfaceSideWith (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {f : Site 2}
    (hf : bac_IsRCoastFace ω n f) : ∃ q : Site 2, crr_InterfaceSideWith ω n f q := by
  obtain ⟨pL, pR, hpL, hpR, hadj, hpLbox, hpRbox, hpLc, hpRc⟩ :=
    crr_rCoastFace_has_interface_side ω n hf
  exact ⟨pR, hpR, pL, hpL, hadj, hpLbox, hpRbox, hpLc, hpRc⟩


end Universality
end StatMech
