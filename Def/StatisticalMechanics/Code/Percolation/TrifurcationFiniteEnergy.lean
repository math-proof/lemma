module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationExistence.Part4
public import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationExistence2.Part3
public import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationConstruction.Part3
public import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationFiniteEnergy
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationFiniteEnergy.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Percolation

variable {d : ℕ}


def tfe_BoxAttachResidue (d n : ℕ) : Prop := tex_BoxAttachData d n


end Percolation
end StatMech
