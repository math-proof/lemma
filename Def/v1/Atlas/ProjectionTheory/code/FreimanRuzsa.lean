/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/FreimanRuzsa.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.ProjectionTheory.code.FreimanRuzsa
open Finset Pointwise


namespace FreimanRuzsa

/-- The finset of points represented by a GAP $P$: all sums
$P.\text{base} + \sum_i n_i \cdot P.\text{dirs}\,i$ for $0 \le n_i < P.\text{lengths}\,i$. -/
noncomputable def GAP.toFinset [DecidableEq α] [AddCommGroup α] (P : GAP α) : Finset α :=
  (Fintype.piFinset (fun i => Finset.range (P.lengths i))).image
    (fun n => P.base + ∑ i : Fin P.dim, (n i) • (P.dirs i))

/-- The volume of a GAP, i.e. the product $\prod_i P.\text{lengths}\,i$ of all the side
lengths. This bounds the cardinality of `P.toFinset`. -/
def GAP.volume [AddCommGroup α] (P : GAP α) : ℕ :=
  ∏ i : Fin P.dim, P.lengths i

end FreimanRuzsa
