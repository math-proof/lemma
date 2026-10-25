/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcNontrivial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FK.CriticalPoint.Part3
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.Limits
import Theorem.StatisticalMechanics.Code.FK.Comparison
import Theorem.StatisticalMechanics.Code.Percolation.PcNontrivial.Part4
import Theorem.StatisticalMechanics.Code.Foundations.MonotoneLimit
import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial
open MeasureTheory Filter Topology Set SimpleGraph
open scoped NNReal ENNReal BigOperators Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.Percolation


variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

variable (bdry : V → Prop) [DecidablePred bdry]


variable {d : ℕ}


def fkExtWord (m : ℕ) (hd : 0 < d) (w : Fin m → Fin d × Bool) : ℕ → Fin d × Bool :=
  fun k => if hk : k < m then w ⟨k, hk⟩ else (⟨0, hd⟩, false)


def fkExistsOpenWalk (d m : ℕ) (hd : 0 < d) : Set (ConfigSpace (Sym2 (Site d))) :=
  ⋃ (w : Fin m → Fin d × Bool) (_ : goodWord (fkExtWord m hd w) m), wordEvent (fkExtWord m hd w) m


end FK
end StatMech
