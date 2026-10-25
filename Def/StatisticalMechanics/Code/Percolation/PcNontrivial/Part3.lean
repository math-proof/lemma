/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcNontrivial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Def.StatisticalMechanics.Code.Percolation.TildePc.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Theorem.StatisticalMechanics.Code.Percolation.PcNontrivial.Part3
open MeasureTheory Set SimpleGraph
open scoped NNReal ENNReal
open Finset

set_option linter.deprecated false
set_option linter.style.longLine false


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


noncomputable def dirOf (hd : 0 < d) {ω : ConfigSpace (Sym2 (Site d))} {v : Site d}
    (q : (openSubgraph d ω).Walk (origin d) v) (k : ℕ) : Fin d × Bool := by
  classical
  exact if hk : k < q.length then
      ((adj_exists_dir (openSubgraph_le ω (q.adj_getVert_succ hk))).choose,
       (adj_exists_dir (openSubgraph_le ω (q.adj_getVert_succ hk))).choose_spec.choose)
    else (⟨0, hd⟩, false)


end Percolation
end StatMech
