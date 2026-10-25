/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.BK.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterion.Part3
open MeasureTheory Finset
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace


variable {E : Type*}


variable {V : Type*}


def ConnToSet (G : SimpleGraph V) (ω : ConfigSpace (Sym2 V)) (A : Set V)
    (u : V) (B : Set V) : Prop :=
  ∃ (hu : u ∈ A) (b : V) (hb : b ∈ A), b ∈ B ∧ ConnWithin G ω A ⟨u, hu⟩ ⟨b, hb⟩


def connEvent (G : SimpleGraph V) (A : Set V) (u : V) (B : Set V) :
    Set (ConfigSpace (Sym2 V)) := {ω | ConnToSet G ω A u B}


def edgeOpenEvent (x y : V) : Set (ConfigSpace (Sym2 V)) := {ω | ω s(x, y) = true}


end Sharpness
end StatMech
