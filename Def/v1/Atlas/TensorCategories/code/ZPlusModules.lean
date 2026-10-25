/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ZPlusModules.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Structure.v1.Atlas.TensorCategories.code.ZPlusModules.Part2
set_option maxHeartbeats 800000


/-- When the index set `ι` is finite, a general `ZPlusRingGen` collapses to a
`ZPlusRing`: the `finsum` associativity becomes an ordinary `Finset.sum`. -/
def ZPlusRingGen.toZPlusRing {ι : Type*} [DecidableEq ι] [Fintype ι]
    (R : ZPlusRingGen ι) : ZPlusRing ι where
  N := R.N
  I₀ := R.I₀
  unit_mul := R.unit_mul
  mul_unit := R.mul_unit
  assoc := fun i j k l => by
    have ⟨_, _, h⟩ := R.assoc i j k l
    rwa [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype] at h

/-- A `ZPlusRing` over a finite index set `ι` can always be regarded as a `ZPlusRingGen`,
since finiteness automatically supplies the finite-support and `finsum` data. -/
def ZPlusRing.toZPlusRingGen {ι : Type*} [DecidableEq ι] [Fintype ι]
    (R : ZPlusRing ι) : ZPlusRingGen ι where
  N := R.N
  I₀ := R.I₀
  finite_support := fun _ _ => Set.Finite.subset (Set.toFinite _) (Set.subset_univ _)
  unit_mul := R.unit_mul
  mul_unit := R.mul_unit
  assoc := fun i j k l =>
    ⟨Set.Finite.subset (Set.toFinite _) (Set.subset_univ _),
     Set.Finite.subset (Set.toFinite _) (Set.subset_univ _),
     by rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]; exact R.assoc i j k l⟩

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The squared coefficient at `k`: the total `∑_{i,j} N(i, j, k)` of structure
constants whose product lands at `k`. This bounds dimensions of irreducible modules. -/
def ZPlusRing.squaredCoeff (R : ZPlusRing ι) (k : ι) : ℕ :=
  ∑ i : ι, ∑ j : ι, R.N i j k

/-- The maximum of `R.squaredCoeff k` over all basis elements `k`, which bounds
the size of any irreducible `ℤ_+`-module over `R`. -/
noncomputable def ZPlusRing.maxSquaredCoeff (R : ZPlusRing ι) [Nonempty ι] : ℕ :=
  Finset.sup' Finset.univ Finset.univ_nonempty R.squaredCoeff

