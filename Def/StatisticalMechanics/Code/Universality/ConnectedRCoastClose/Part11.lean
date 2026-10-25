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
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part10
open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped NNReal
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

def crr_LeftFillFrameArcOrder (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  ∀ (f₁ f₂ q₁ q₂ : Site 2),
    crr_InterfaceSideWith ω n f₁ q₁ → crr_InterfaceSideWith ω n f₂ q₂ →
    ∀ (h1 : q₁ ∈ bac_boxMinusL ω n) (h2 : q₂ ∈ bac_boxMinusL ω n),
      ((hypercubicLattice 2).induce (bac_boxMinusL ω n)).Reachable ⟨q₁, h1⟩ ⟨q₂, h2⟩ →
      ∃ c : (faceBoundaryGraph (crr_leftFill ω n)).Walk f₁ f₁,
        ∃ hf₂ : f₂ ∈ c.support,
          (∀ f g : Site 2, s(f, g) ∈ (c.takeUntil f₂ hf₂).edges →
            crc2_IsBoxInteriorEdge n f g) ∨
          (∀ f g : Site 2, s(f, g) ∈ (c.dropUntil f₂ hf₂).edges →
            crc2_IsBoxInteriorEdge n f g)


def crr_LeftFillInteriorArc (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  ∀ (f₁ f₂ q₁ q₂ : Site 2),
    crr_InterfaceSideWith ω n f₁ q₁ → crr_InterfaceSideWith ω n f₂ q₂ →
    ∀ (h1 : q₁ ∈ bac_boxMinusL ω n) (h2 : q₂ ∈ bac_boxMinusL ω n),
      ((hypercubicLattice 2).induce (bac_boxMinusL ω n)).Reachable ⟨q₁, h1⟩ ⟨q₂, h2⟩ →
      ∃ w : (faceBoundaryGraph (crr_leftFill ω n)).Walk f₁ f₂,
        ∀ f g : Site 2, s(f, g) ∈ w.edges → crc2_IsBoxInteriorEdge n f g


end Universality
end StatMech
