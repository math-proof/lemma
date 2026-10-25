/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonCoarseTrifurcationGeneral.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonSingleSiteStability.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.MultivaluedMap
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonStep3Bridge.Part2
open MeasureTheory Set
open scoped ENNReal


namespace StatMech.FrontierA

open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}


def TripleEventIgnoresHighAt (x : Site d) (A : Set (FieldTriple d)) : Prop :=
  ∀ q q' : FieldTriple d, q.1 = q'.1 → q.2.1 = q'.2.1 →
    (∀ y ≠ x, q.2.2 y = q'.2.2 y) → (q ∈ A ↔ q' ∈ A)


def HasHighInsertionLowerBound (mu : Measure (FieldTriple d))
    (t : NNReal) (epsilon : ℝ≥0∞) : Prop :=
  ∀ (x : Site d) (A : Set (FieldTriple d)), MeasurableSet A →
    TripleEventIgnoresHighAt x A →
    epsilon * mu A ≤ mu (A ∩ {q | t ≤ q.2.2 x})


def TripleEventIgnoresHighOn (S : Finset (Site d))
    (A : Set (FieldTriple d)) : Prop :=
  ∀ q q' : FieldTriple d, q.1 = q'.1 → q.2.1 = q'.2.1 →
    (∀ y ∉ S, q.2.2 y = q'.2.2 y) → (q ∈ A ↔ q' ∈ A)


def highThresholdOn (t : NNReal) (S : Finset (Site d)) :
    Set (FieldTriple d) :=
  {q | ∀ x ∈ S, t ≤ q.2.2 x}

end StatMech.FrontierA
