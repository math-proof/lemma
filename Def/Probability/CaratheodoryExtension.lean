/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/CaratheodoryExtension.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
public import Mathlib.MeasureTheory.SetAlgebra
public import Mathlib.MeasureTheory.Measure.MeasureSpace

@[expose] public section

open scoped ENNReal


noncomputable section

open Set MeasureTheory MeasureTheory.Measure MeasurableSpace

/-- Every set algebra is a set semiring: combine the set-ring structure (empty set,
closure under union, closure under difference) and view the resulting ring as a
semiring. -/
def isSetSemiring_of_isSetAlgebra {α : Type*} {𝒜 : Set (Set α)} (h : IsSetAlgebra 𝒜) :
    IsSetSemiring 𝒜 :=
  (IsSetRing.mk h.empty_mem (fun {_} {_} hs ht => h.union_mem hs ht)
    (fun {_} {_} hs ht => h.diff_mem hs ht)).isSetSemiring

end
