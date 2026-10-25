/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/SubdivisionSmall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section6
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section6
import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Algebra.Order.Archimedean.Basic
import Theorem.v1.Atlas.AlgebraicTopologyI.code.SubdivisionSmall


noncomputable section

namespace AlgebraicTopologyI

variable {X : Type*} [TopologicalSpace X]

/-- The `i`-th barycentric coordinate of the `k`-th vertex of the simplex of the standard
barycentric subdivision associated to the permutation `π`. It is `1/(k+1)` when `i` is in
the image under `π` of `{0, …, k}`, and `0` otherwise. -/
def barySubdivVertex (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1))
    (i : Fin (n + 1)) : ℝ :=
  if ∃ j : Fin (n + 1), j ≤ k ∧ π j = i then 1 / ((k : ℝ) + 1) else 0

/-- The underlying function of the barycentric subdivision map associated to a permutation
`π`: it sends a barycentric coordinate vector `t` to the affine combination of the
barycentric subdivision vertices weighted by `t`. -/
def barySubdivMapFn (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (t : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  ∑ k : Fin (n + 1), t k * barySubdivVertex n π k i

end AlgebraicTopologyI
end
