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
import Theorem.StatisticalMechanics.Code.Universality.PlanarMengerDualityClose.Part2
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

def pmd_boxFaceBarrier (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : SimpleGraph (Site 2) where
  Adj f g := (hypercubicLattice 2).Adj f g ∧
    ∃ p q : Site 2, sharedPrimalEdge f g = s(p, q) ∧
      bdEdge (bcd_leftReach ω n) s(p, q) ∧ p ∈ rect 0 n 0 n ∧ q ∈ rect 0 n 0 n
  symm := by
    constructor
    rintro f g ⟨hadj, p, q, hpq, hbd, hp, hq⟩
    refine ⟨hadj.symm, q, p, ?_, ?_, hq, hp⟩
    · rw [← sharedPrimalEdge_comm_of_adj hadj, hpq, Sym2.eq_swap]
    · rwa [Sym2.eq_swap]
  loopless := ⟨fun f h => (hypercubicLattice 2).irrefl h.1⟩

end Universality
end StatMech
