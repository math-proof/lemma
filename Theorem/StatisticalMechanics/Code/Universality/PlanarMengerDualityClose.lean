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
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem pmd_faceVAdj_of_closed (ω : ConfigSpace (Sym2 (Site 2))) (a b : ℤ)
    (hcl : ω s(![a, b + 1], ![a + 1, b + 1]) = false) :
    (fci_faceOpenDual ω).Adj ![a, b] ![a, b + 1] := by
  refine ⟨by simp [hypercubicLattice_adj, Fin.sum_univ_two], ?_⟩
  rw [sharedPrimalEdge_top]; unfold faceCorner01 faceCorner11; exact hcl


theorem pmd_faceHAdj_of_closed (ω : ConfigSpace (Sym2 (Site 2))) (a b : ℤ)
    (hcl : ω s(![a + 1, b], ![a + 1, b + 1]) = false) :
    (fci_faceOpenDual ω).Adj ![a, b] ![a + 1, b] := by
  refine ⟨by simp [hypercubicLattice_adj, Fin.sum_univ_two], ?_⟩
  rw [sharedPrimalEdge_right]; unfold faceCorner10 faceCorner11; exact hcl


end Universality
end StatMech
