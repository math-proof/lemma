/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivative.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
import Def.StatisticalMechanics.Code.FK.RussoDerivative.Part4
open scoped BigOperators


namespace StatMech

namespace FK

open Finset ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem hasDerivAt_fkProbOf {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {q : ℝ} (hq : 0 < q)
    (A : Set (ConfigSpace (Sym2 V))) :
    HasDerivAt (fun p => fkProbOf G p q A)
      ((∑ e ∈ G.edgeFinset, fkCov G p q (A.indicator (fun _ => (1 : ℝ))) (coord e))
        / (p * (1 - p))) p :=
  hasDerivAt_fkMean G hp hp1 hq _


theorem deriv_fkProbOf {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {q : ℝ} (hq : 0 < q)
    (A : Set (ConfigSpace (Sym2 V))) :
    deriv (fun p => fkProbOf G p q A) p
      = (∑ e ∈ G.edgeFinset, fkCov G p q (A.indicator (fun _ => (1 : ℝ))) (coord e))
        / (p * (1 - p)) :=
  (hasDerivAt_fkProbOf G hp hp1 hq A).deriv


end FK
end StatMech
