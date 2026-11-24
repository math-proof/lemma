module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplex.Part3
public import Theorem.StatisticalMechanics.Code.Ising.GibbsExtreme
public import Theorem.StatisticalMechanics.Code.Foundations.StochasticDomination
open MeasureTheory ProbabilityTheory MeasurableSpace Set
open scoped BigOperators ENNReal StatMech
set_option linter.style.longLine false
set_option linter.unusedSectionVars false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsChoquet.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


variable {E : Type*}


def upMeasSystem (E : Type*) : Set (Set (ConfigSpace E)) :=
  {A | MeasurableSet A ∧ IsUpperSet A}


end Ising
end StatMech
