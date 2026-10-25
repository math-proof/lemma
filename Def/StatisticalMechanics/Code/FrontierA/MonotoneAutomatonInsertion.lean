/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInsertion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonInterpolation.Part3
open MeasureTheory
open scoped ENNReal NNReal


namespace StatMech.FrontierA

open StatMech.Lattice

variable {d : ℕ}


def SiteEventIgnores (x : Site d) (B : Set (ConfigSpace (Site d))) : Prop :=
  ∀ eta eta' : ConfigSpace (Site d),
    (∀ y, y ≠ x → eta y = eta' y) → (eta ∈ B ↔ eta' ∈ B)


def TripleEventIgnoresMiddleAt (x : Site d) (A : Set (FieldTriple d)) : Prop :=
  ∀ q q' : FieldTriple d,
    q.1 = q'.1 →
    (∀ y, y ≠ x → q.2.1 y = q'.2.1 y) →
    (q ∈ A ↔ q' ∈ A)


def HasMiddleInsertionLowerBound (mu : Measure (FieldTriple d))
    (t : ℝ≥0) (epsilon : ℝ≥0∞) : Prop :=
  ∀ (x : Site d) (A : Set (FieldTriple d)), MeasurableSet A →
    TripleEventIgnoresMiddleAt x A →
    epsilon * mu A ≤ mu (A ∩ {q | t ≤ q.2.1 x})


def HasSiteInsertionLowerBound (nu : Measure (ConfigSpace (Site d)))
    (epsilon : ℝ≥0∞) : Prop :=
  ∀ (x : Site d) (B : Set (ConfigSpace (Site d))), MeasurableSet B →
    SiteEventIgnores x B →
    epsilon * nu B ≤ nu (B ∩ {eta | eta x = true})


end StatMech.FrontierA
