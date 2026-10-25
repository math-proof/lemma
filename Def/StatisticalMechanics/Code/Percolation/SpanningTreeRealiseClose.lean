/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeRealiseClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ForestLeafCountClose.Part4
import Abbrev.StatisticalMechanics.Code.Percolation.SpanningTreeRealiseClose
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


def str_sAdj {N : Type*} [DecidableEq N] (a b : str_SpiderV N) : Bool :=
  match a, b with
  | none, some (Sum.inl _) => true
  | some (Sum.inl _), none => true
  | some (Sum.inl i), some (Sum.inr p) => decide (i = p.1)
  | some (Sum.inr p), some (Sum.inl i) => decide (i = p.1)
  | _, _ => false


def str_spiderG (N : Type*) [DecidableEq N] : SimpleGraph (str_SpiderV N) :=
  SimpleGraph.fromRel (fun a b => str_sAdj a b = true)

end Percolation
end StatMech
