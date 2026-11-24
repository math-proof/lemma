module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.FK.InducedBC.Part11
public import Theorem.StatisticalMechanics.Code.FK.WiredDomChain.Part4
public import Theorem.StatisticalMechanics.Code.FK.Limits
public import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
public import Theorem.StatisticalMechanics.Code.Foundations.MonotoneLimit
public import Theorem.StatisticalMechanics.Code.Foundations.WeakConvergence
public import Def.StatisticalMechanics.Code.FK.FreeWeakLimit
open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK

variable {d : ℕ}


noncomputable instance instDecidableRelInducedWiringFree (d n : ℕ)
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) : DecidableRel (inducedWiringFree d n ψ).Adj :=
  fun _ _ => Classical.dec _

end FK
end StatMech
