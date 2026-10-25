/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCircuitToWalk.lean -/

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
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Theorem.StatisticalMechanics.Code.Universality.DualCircuitToWalk
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}


def dcw_dualBarrierGraph (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    SimpleGraph (Site 2) where
  Adj p q :=
    ∃ v w : Site 2, dcw_isBarrierEdge ω n v w ∧
      ((p = rot90Fun v ∧ q = rot90Fun w) ∨ (p = rot90Fun w ∧ q = rot90Fun v))
  symm := by
    constructor
    rintro p q ⟨v, w, hvw, (⟨hp, hq⟩ | ⟨hp, hq⟩)⟩
    · exact ⟨v, w, hvw, Or.inr ⟨hq, hp⟩⟩
    · exact ⟨v, w, hvw, Or.inl ⟨hq, hp⟩⟩
  loopless := by
    refine ⟨fun p hp => ?_⟩
    have hinj : Function.Injective rot90Fun := rot90Equiv.injective
    rcases hp with ⟨v, w, hvw, (⟨hp, hq⟩ | ⟨hp, hq⟩)⟩
    · rw [hp] at hq
      exact (hypercubicLattice 2).ne_of_adj hvw.2.2.2 (hinj hq)
    · rw [hp] at hq
      exact (hypercubicLattice 2).ne_of_adj hvw.2.2.2 (hinj hq.symm)


end Universality
end StatMech
