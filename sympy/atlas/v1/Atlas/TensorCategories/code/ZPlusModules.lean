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

set_option maxHeartbeats 800000

/-- A `ℤ_+`-ring (general version, not requiring `ι` to be finite): a set `ι` of
distinguished basis elements with nonnegative integer structure constants `N i j k`
satisfying unitality and associativity, and with finite multiplicative support. -/
structure ZPlusRingGen (ι : Type*) [DecidableEq ι] where
  N : ι → ι → ι → ℕ
  I₀ : Finset ι
  finite_support : ∀ i j, Set.Finite {k | N i j k ≠ 0}
  unit_mul : ∀ j k, ∑ s ∈ I₀, N s j k = if j = k then 1 else 0
  mul_unit : ∀ i k, ∑ s ∈ I₀, N i s k = if i = k then 1 else 0
  assoc : ∀ i j k l,
    Set.Finite {m | N i j m * N m k l ≠ 0} ∧
    Set.Finite {m | N j k m * N i m l ≠ 0} ∧
    ∑ᶠ m, N i j m * N m k l = ∑ᶠ m, N j k m * N i m l

/-- Alias for Definition 1.42.1 of Etingof–Gelaki–Nikshych–Ostrik: a `ℤ_+`-ring is the
general (possibly infinite-index) version `ZPlusRingGen`. -/
abbrev Definition_1_42_1 := ZPlusRingGen

/-- A `ℤ_+`-ring with finite index set `ι`: nonnegative integer structure constants
`N i j k`, a unit subset `I₀`, and the unitality and associativity axioms expressed
with ordinary finite sums. -/
structure ZPlusRing (ι : Type*) [DecidableEq ι] [Fintype ι] where
  N : ι → ι → ι → ℕ
  I₀ : Finset ι
  unit_mul : ∀ j k, ∑ s ∈ I₀, N s j k = if j = k then 1 else 0
  mul_unit : ∀ i k, ∑ s ∈ I₀, N i s k = if i = k then 1 else 0
  assoc : ∀ i j k l, ∑ m : ι, N i j m * N m k l = ∑ m : ι, N j k m * N i m l

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

/-- A `ℤ_+`-module over a `ℤ_+`-ring `R`: a finite basis set `κ` together with
nonnegative integer action constants `act i l k`, satisfying unitality from `R.I₀`
and a compatibility expressing associativity of the action. -/
structure ZPlusModule (R : ZPlusRing ι) (κ : Type*) [DecidableEq κ] [Fintype κ] where
  act : ι → κ → κ → ℕ
  act_unit : ∀ l k, ∑ s ∈ R.I₀, act s l k = if l = k then 1 else 0
  act_compat : ∀ i j l k,
    ∑ m : ι, R.N i j m * act m l k = ∑ n : κ, act j l n * act i n k

/-- Alias for Definition 2.8.1 of Etingof–Gelaki–Nikshych–Ostrik: a `ℤ_+`-module
over a `ℤ_+`-ring is what `ZPlusModule` formalizes. -/
abbrev Definition_2_8_1 := @ZPlusModule

variable {R : ZPlusRing ι} {κ : Type*} [DecidableEq κ] [Fintype κ]

namespace ZPlusModule

variable (M : ZPlusModule R κ)

/-- A nonempty proper subset `S ⊆ κ` is a `ℤ_+`-submodule of `M` if it is closed
under the action: `M.act i l k ≠ 0` and `l ∈ S` implies `k ∈ S`. -/
structure IsZPlusSubmodule (S : Finset κ) : Prop where
  nonempty : S.Nonempty
  proper : S ≠ Finset.univ
  closed : ∀ (i : ι) (l : κ), l ∈ S → ∀ (k : κ), M.act i l k ≠ 0 → k ∈ S

/-- A `ℤ_+`-module is irreducible if it has no proper nonempty `ℤ_+`-submodule. -/
def IsIrreducible : Prop := ∀ S : Finset κ, ¬M.IsZPlusSubmodule S

/-- Alias for Definition 2.8.3: irreducibility of a `ℤ_+`-module. -/
abbrev def_2_8_3 : Prop := M.IsIrreducible

/-- The sum `∑_{k} act(i, l, k)` of action coefficients of `i ∈ ι` acting on `l ∈ κ`. -/
def actCoeffSum (i : ι) (l : κ) : ℕ := ∑ k : κ, M.act i l k

/-- The total action coefficient at `l ∈ κ`: the sum over all `i ∈ ι` of `actCoeffSum i l`. -/
def totalActCoeff (l : κ) : ℕ := ∑ i : ι, M.actCoeffSum i l

/-- The regular `ℤ_+`-module of a `ℤ_+`-ring `R`: `R` acting on its own basis `ι`
via the structure constants `N`. -/
def regularModule (R : ZPlusRing ι) : ZPlusModule R ι where
  act := R.N
  act_unit := R.unit_mul
  act_compat := R.assoc

/-- A morphism of `ℤ_+`-modules over the same `ℤ_+`-ring `R`: a nonnegative integer
matrix `toMatrix : κ₁ → κ₂ → ℕ` that intertwines the two actions of `R`. -/
structure ZPlusModuleHom {κ₁ κ₂ : Type*} [DecidableEq κ₁] [Fintype κ₁]
    [DecidableEq κ₂] [Fintype κ₂]
    (M₁ : ZPlusModule R κ₁) (M₂ : ZPlusModule R κ₂) where
  toMatrix : κ₁ → κ₂ → ℕ
  equivariant : ∀ (i : ι) (l : κ₁) (k₂ : κ₂),
    ∑ k₁ : κ₁, M₁.act i l k₁ * toMatrix k₁ k₂ =
    ∑ n : κ₂, toMatrix l n * M₂.act i n k₂

/-- An isomorphism between two `ℤ_+`-modules: a bijection of basis sets `κ₁ ≃ κ₂`
that intertwines the two actions of `R`. -/
structure IsIsomorphism {κ₁ κ₂ : Type*} [DecidableEq κ₁] [Fintype κ₁]
    [DecidableEq κ₂] [Fintype κ₂]
    (M₁ : ZPlusModule R κ₁) (M₂ : ZPlusModule R κ₂) where
  equiv : κ₁ ≃ κ₂
  compat : ∀ (i : ι) (l k : κ₁), M₁.act i l k = M₂.act i (equiv l) (equiv k)

/-- A `ℤ_+`-module is indecomposable if its basis `κ` cannot be split into two
nonempty disjoint action-closed subsets covering `κ`. -/
def IsIndecomposable : Prop :=
  ∀ (S₁ S₂ : Finset κ),
    S₁.Nonempty → S₂.Nonempty → Disjoint S₁ S₂ → S₁ ∪ S₂ = Finset.univ →
    (∀ (i : ι) (l : κ), l ∈ S₁ → ∀ (k : κ), M.act i l k ≠ 0 → k ∈ S₁) →
    (∀ (i : ι) (l : κ), l ∈ S₂ → ∀ (k : κ), M.act i l k ≠ 0 → k ∈ S₂) →
    False

/-- Exactness of a `ℤ_+`-module: whenever `act i l k ≠ 0` there exists some `j ∈ ι`
with `act j k l ≠ 0`, i.e. the action is symmetric up to relabeling. -/
def IsExact : Prop :=
  ∀ (i : ι) (l k : κ), M.act i l k ≠ 0 → ∃ j : ι, M.act j k l ≠ 0

/-- A subset `S ⊆ κ` is action-closed under `M` if whenever `l ∈ S` and
`M.act i l k ≠ 0` we have `k ∈ S`. -/
def IsActionClosed (S : Finset κ) : Prop :=
  ∀ (i : ι) (l : κ), l ∈ S → ∀ (k : κ), M.act i l k ≠ 0 → k ∈ S

/-- An action-closed subset `S ⊆ κ` is an indecomposable piece if it cannot be
partitioned into two nonempty disjoint action-closed subsets. -/
def IsIndecomposablePiece (S : Finset κ) : Prop :=
  ∀ (S₁ S₂ : Finset κ),
    S₁.Nonempty → S₂.Nonempty → Disjoint S₁ S₂ → S₁ ∪ S₂ = S →
    M.IsActionClosed S₁ → M.IsActionClosed S₂ → False

/-- An action-closed subset `S ⊆ κ` is an irreducible piece if it contains no
proper nonempty action-closed subset. -/
def IsIrreduciblePiece (S : Finset κ) : Prop :=
  ∀ T : Finset κ, T.Nonempty → T ≠ S → T ⊆ S → ¬M.IsActionClosed T

/-- A `ℤ_+`-decomposition of `M`: a finite family of nonempty pairwise disjoint
action-closed subsets of `κ` whose union covers `κ`. -/
structure IsZPlusDecomposition (parts : Finset (Finset κ)) : Prop where
  covers : ∀ k : κ, ∃ P ∈ parts, k ∈ P
  pairwise_disjoint : ∀ P₁ ∈ parts, ∀ P₂ ∈ parts, P₁ ≠ P₂ → Disjoint P₁ P₂
  nonempty : ∀ P ∈ parts, P.Nonempty
  closed : ∀ P ∈ parts, M.IsActionClosed P
