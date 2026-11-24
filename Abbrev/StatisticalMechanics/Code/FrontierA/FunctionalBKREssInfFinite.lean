module
public import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralDual.Part4
public import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralFinite
public import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
public import Mathlib.MeasureTheory.Function.EssSup
open MeasureTheory
open scoped BigOperators ENNReal NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKREssInfFinite.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech StatMech.ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


abbrev AgreementFiberPoint (K : Set E) (omega : ConfigSpace E) :=
  {eta : ConfigSpace E // agreeOn K omega eta}


end StatMech.FrontierA
