/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivative.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
import Def.StatisticalMechanics.Code.FK.RussoDerivative.Part5
open scoped BigOperators


namespace StatMech

namespace FK

open Finset ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


lemma russoPrefactor_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : 0 < russoPrefactor p :=
  one_div_pos.2 (mul_pos hp (by linarith))


theorem russo_bound {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {q : ℝ} (hq : 0 < q)
    (A : Set (ConfigSpace (Sym2 V))) :
    russoPrefactor p * (∑ e ∈ G.edgeFinset,
        fkCov G p q (A.indicator (fun _ => (1 : ℝ))) (coord e))
      ≤ deriv (fun p => fkProbOf G p q A) p := by
  rw [deriv_fkProbOf G hp hp1 hq A]
  unfold russoPrefactor
  rw [one_div, div_eq_inv_mul]

end FK
end StatMech
