/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivative.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
import Def.StatisticalMechanics.Code.FK.RussoDerivative
open scoped BigOperators


namespace StatMech

namespace FK

open Finset ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in


lemma hasDerivAt_edgeFactor (ω : ConfigSpace (Sym2 V)) (e : Sym2 V) (p : ℝ) :
    HasDerivAt (fun p => if ω e then p else 1 - p) (if ω e then (1 : ℝ) else -1) p := by
  by_cases h : ω e
  · simp only [h, if_true]; exact hasDerivAt_id p
  · simp only [h]
    simpa using (hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p)


end FK
end StatMech
