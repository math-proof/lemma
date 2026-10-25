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
import Theorem.v1.Atlas.AlgebraicTopologyI.code.SubdivisionSmall.Part2


noncomputable section

namespace AlgebraicTopologyI

variable {X : Type*} [TopologicalSpace X]

/-- The singular `n`-simplex on the standard `n`-simplex associated to a permutation `π`
of `{0,…,n}`, given by the barycentric subdivision construction. -/
def barySubdivSimplex (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) :
    SingularSimplex n ↥(stdSimplex ℝ (Fin (n + 1))) :=
  ⟨fun t => ⟨barySubdivMapFn n π t.1, barySubdivMapFn_mem n π t.1 t.2⟩,
    barySubdivMap_continuous n π⟩

/-- The standard subdivision chain on the standard `n`-simplex, defined as the signed sum
over permutations `π` of `Fin (n+1)` of the barycentric subdivision simplices, with sign
given by `Equiv.Perm.sign π`. -/
def stdSubdivisionChain (n : ℕ) :
    SingularChains n ↥(stdSimplex ℝ (Fin (n + 1))) :=
  ∑ π : Equiv.Perm (Fin (n + 1)),
    (Equiv.Perm.sign π : ℤ) • FreeAbelianGroup.of (barySubdivSimplex n π)

/-- The subdivision operator `$ : S_n(X) → S_n(X)`, defined on a singular simplex `σ` as
the image of the standard subdivision chain under `σ`, and extended additively. -/
def subdivisionOp (n : ℕ) (X : Type*) [TopologicalSpace X] :
    SingularChains n X →+ SingularChains n X :=
  FreeAbelianGroup.lift (fun σ : SingularSimplex n X =>
    SingularChains.map σ (stdSubdivisionChain n))

/-- The `k`-fold iterate `$^k c` of the subdivision operator applied to a chain `c`. -/
def iterateSubdivision {n : ℕ} (k : ℕ) (c : SingularChains n X) : SingularChains n X :=
  ((⇑(subdivisionOp n X))^[k]) c

/-- The (finite) set of singular simplices that appear with nonzero coefficient in the
chain `c`. -/
def supportOfChain {n : ℕ} (c : SingularChains n X) : Finset (SingularSimplex n X) :=
  FreeAbelianGroup.support (show FreeAbelianGroup (SingularSimplex n X) from c)

/-- A chain is `𝒜`-small if every singular simplex appearing in its support is
`𝒜`-small (i.e. has image contained in some member of `𝒜`). -/
def IsSmallChain (𝒜 : Set (Set X)) {n : ℕ} (c : SingularChains n X) : Prop :=
  ∀ σ ∈ supportOfChain c, IsSmall 𝒜 σ

end AlgebraicTopologyI
end
