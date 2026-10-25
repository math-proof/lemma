/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarMengerDualityClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.FaceDualDichotomy
import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomyClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWDualVCrossingClose.Part2
import Def.StatisticalMechanics.Code.Universality.PlanarMengerDualityClose
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem pmd_faceDualVCrossing_of_spanningContour (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {u : Site 2} (c : (fci_faceOpenDual ω).Walk u u)
    {a₀ a₁ : ℤ} (ha0 : 0 ≤ a₀) (ha0' : a₀ ≤ n - 1) (ha1 : 0 ≤ a₁) (ha1' : a₁ ≤ n - 1)
    (hbot : (![a₀, -1] : Site 2) ∈ c.support) (htop : (![a₁, n] : Site 2) ∈ c.support) :
    pmd_FaceDualVCrossing ω n := by
  classical
  refine ⟨a₀, a₁, ha0, ha0', ha1, ha1', ?_⟩
  exact (Reachable.symm ⟨c.takeUntil _ hbot⟩).trans ⟨c.takeUntil _ htop⟩


theorem pmd_faceDualV_implies_spanningReach (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (h : pmd_FaceDualVCrossing ω n) :
    ∃ (a₀ a₁ : ℤ), (fci_faceOpenDual ω).Reachable ![a₀, -1] ![a₁, n] := by
  obtain ⟨a₀, a₁, _, _, _, _, hreach⟩ := h
  exact ⟨a₀, a₁, hreach⟩


end Universality
end StatMech
