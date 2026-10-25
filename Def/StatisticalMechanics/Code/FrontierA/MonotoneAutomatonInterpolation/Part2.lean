/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInterpolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonLaw.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonInterpolation
open MeasureTheory


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}


def IsTripleFieldTranslationInvariant (mu : Measure (FieldTriple d)) : Prop :=
  ∀ g : Multiplicative (Site d),
    MeasurePreserving (tripleFieldShift g : FieldTriple d → FieldTriple d) mu mu


def IsTripleFieldErgodic (mu : Measure (FieldTriple d)) : Prop :=
  IsTripleFieldTranslationInvariant mu ∧
    ∀ s : Set (FieldTriple d), MeasurableSet s →
      (∀ g : Multiplicative (Site d),
        (tripleFieldShift g : FieldTriple d → FieldTriple d) ⁻¹' s = s) →
      mu s = 0 ∨ mu s = mu Set.univ


def IsMonotoneFieldTriple (q : FieldTriple d) : Prop :=
  q.1 ≤ q.2.1 ∧ q.2.1 ≤ q.2.2


noncomputable def interpolatedSite (T : MonotoneAutomaton d) (q : FieldTriple d) :
    ConfigSpace (Site d) := fun x =>
  T q.1 x || decide (T.threshold ≤ q.2.1 x)

end StatMech.FrontierA
