module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplex.Part3
public import Theorem.StatisticalMechanics.Code.Ising.GibbsExtreme
public import Theorem.StatisticalMechanics.Code.Ising.GibbsChoquet.Part2
public import Theorem.StatisticalMechanics.Code.Foundations.StochasticDomination
public import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplexInfinite.Part2
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology
open scoped BigOperators ENNReal StatMech
set_option linter.style.longLine false
set_option linter.unusedSectionVars false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplexInfinite.lean -/
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


def clopenUpSystem (E : Type*) : Set (Set (ConfigSpace E)) :=
  {A | IsClopen A ∧ IsUpperSet A}


end Ising
end StatMech
