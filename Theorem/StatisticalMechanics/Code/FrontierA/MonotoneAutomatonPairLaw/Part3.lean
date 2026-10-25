/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonPairLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonInterpolation.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.MassTransport
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonPairLaw.Part3
open MeasureTheory


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


theorem interpolatedHighPairLaw_isTranslationInvariant
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    (hinv : IsTripleFieldTranslationInvariant mu) :
    IsTranslationInvariant (G := Multiplicative (Site d))
      (interpolatedHighPairLaw T mu) := by
  intro g
  refine ⟨measurable_shift g, ?_⟩
  unfold interpolatedHighPairLaw
  rw [Measure.map_map (measurable_shift g) (measurable_interpolatedHighPair T)]
  have hcomp :
      (shift g : PairSiteConfig d → PairSiteConfig d) ∘ interpolatedHighPair T =
        interpolatedHighPair T ∘ (tripleFieldShift g : FieldTriple d → FieldTriple d) := by
    funext q
    exact (interpolatedHighPair_shift T g q).symm
  rw [hcomp,
    ← Measure.map_map (measurable_interpolatedHighPair T)
      (measurable_tripleFieldShift g),
    (hinv g).map_eq]


theorem interpolatedHighPair_nested (T : MonotoneAutomaton d)
    (q : FieldTriple d) (hq : IsMonotoneFieldTriple q) :
    pairSiteLeft (interpolatedHighPair T q) ≤
      pairSiteRight (interpolatedHighPair T q) :=
  (monotoneAutomaton_interpolation_sandwich T q hq).2.1.trans
    (monotoneAutomaton_interpolation_sandwich T q hq).2.2

end StatMech.FrontierA
