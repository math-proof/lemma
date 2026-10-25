/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonSiteBond.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonLaw
open MeasureTheory
open scoped NNReal


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}


def IsFieldTranslationInvariant (mu : Measure (NonnegativeField d)) : Prop :=
  ∀ g : Multiplicative (Site d),
    MeasurePreserving (fieldShift g : NonnegativeField d → NonnegativeField d) mu mu


def IsFieldErgodic (mu : Measure (NonnegativeField d)) : Prop :=
  IsFieldTranslationInvariant mu ∧
    ∀ s : Set (NonnegativeField d), MeasurableSet s →
      (∀ g : Multiplicative (Site d),
        (fieldShift g : NonnegativeField d → NonnegativeField d) ⁻¹' s = s) →
      mu s = 0 ∨ mu s = mu Set.univ


def raiseField (xi : NonnegativeField d) (x : Site d) (r : ℝ≥0) :
    NonnegativeField d := fun y => if y = x then max r (xi x) else xi y

end StatMech.FrontierA
