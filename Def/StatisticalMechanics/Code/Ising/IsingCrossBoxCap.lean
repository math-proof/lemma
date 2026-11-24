module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
public import Theorem.StatisticalMechanics.Code.Ising.GibbsExtreme
public import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
public import Theorem.StatisticalMechanics.Code.Ising.IsingPlusErgodicClose
public import Theorem.StatisticalMechanics.Code.FK.FKMixingUpperClose.Part5
public import Theorem.StatisticalMechanics.Code.FK.ErgodicExtremeUpgrade
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
public import Theorem.StatisticalMechanics.Code.Ising.IsingCrossBoxCap
open MeasureTheory Filter Topology Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators
set_option linter.style.longLine false
set_option linter.unusedSectionVars false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingCrossBoxCap.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Ising

open StatMech.FK

open StatMech.Percolation

variable {d : ℕ}


noncomputable def icb_shiftVec {d : ℕ} (i₀ : Fin d) (R : ℤ) : Site d :=
  fun i => if i = i₀ then R else 0


end Ising
end StatMech
