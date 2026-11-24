module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.FK.BoundaryDecay
public import Theorem.StatisticalMechanics.Code.FK.FKUniquenessClose3
public import Theorem.StatisticalMechanics.Code.FK.FKUniquenessClose2
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DecayOfCorrelations.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK ConfigSpace

variable {d : ℕ}


noncomputable def docGap (d N : ℕ) (eb : Sym2 (boxVerts d N)) (p : ℝ) : ℝ :=
  wiredEdgeDensity d 2 (edgeIncl d N eb) p - freeEdgeDensity d 2 (edgeIncl d N eb) p


end FK
end StatMech
