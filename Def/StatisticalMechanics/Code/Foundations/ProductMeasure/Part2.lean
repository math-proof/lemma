/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ProductMeasure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace StatMech

variable {E : Type*}


noncomputable def bernoulliProductMeasure (p : NNReal) (hp : p ≤ 1) :
    Measure (ConfigSpace E) :=
  Measure.infinitePi (fun _ : E => bernoulliMeasure p hp)


end StatMech
