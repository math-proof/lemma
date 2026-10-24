/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/SubdivisionSmall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section6
import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section6
import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Algebra.Order.Archimedean.Basic

noncomputable section

open Classical in
/-- The image of a `Finsupp` under `Finsupp.toFreeAbelianGroup` is the finite sum of the
generators weighted by the corresponding integer coefficients. -/
lemma toFreeAbelianGroup_eq_sum {Y : Type*} (f : Y →₀ ℤ) :
    Finsupp.toFreeAbelianGroup f = f.sum (fun x n => n • FreeAbelianGroup.of x) := by
  simp only [Finsupp.toFreeAbelianGroup, Finsupp.liftAddHom_apply]; congr 1

open Classical in
/-- Any element of a free abelian group can be written as the finite sum of its generators
weighted by the integer coefficients given by its associated `Finsupp`. -/
lemma freeAbelianGroup_eq_sum {Y : Type*} (c : FreeAbelianGroup Y) :
    c = (FreeAbelianGroup.toFinsupp c).sum (fun x n => n • FreeAbelianGroup.of x) := by
  rw [← toFreeAbelianGroup_eq_sum, Finsupp.toFreeAbelianGroup_toFinsupp]

open Classical in
/-- The lift of `f : Y → Z` along `FreeAbelianGroup.lift` evaluated at `c` equals the
finite sum, over the support of `c`, of `f` applied to each generator scaled by its
integer coefficient. -/
lemma lift_eq_finsupp_sum {Y Z : Type*} [AddCommGroup Z] (f : Y → Z)
    (c : FreeAbelianGroup Y) :
    (FreeAbelianGroup.lift f) c =
    (FreeAbelianGroup.toFinsupp c).sum (fun x n => n • f x) := by
  conv_lhs => rw [freeAbelianGroup_eq_sum c]
  simp only [Finsupp.sum, map_sum, map_zsmul, FreeAbelianGroup.lift_apply_of]

open Classical in
/-- The support of a finite sum of free-abelian-group elements is contained in the union
of the supports of the summands. -/
lemma support_finset_sum {Y Z : Type*}
    (s : Finset Y) (f : Y → FreeAbelianGroup Z) :
    (∑ i ∈ s, f i).support ⊆ s.biUnion (fun i => (f i).support) := by
  induction s using Finset.induction with
  | empty => simp [FreeAbelianGroup.support_zero]
  | @insert x s' hxs ih =>
    intro τ hτ
    rw [Finset.sum_insert hxs] at hτ
    rcases Finset.mem_union.mp (FreeAbelianGroup.support_add _ _ hτ) with h | h
    · exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_insert_self _ _, h⟩
    · obtain ⟨y, hy, hfy⟩ := Finset.mem_biUnion.mp (ih h)
      exact Finset.mem_biUnion.mpr ⟨y, Finset.mem_insert_of_mem hy, hfy⟩

open Classical in
/-- The support of `FreeAbelianGroup.lift f c` is contained in the union over the support
of `c` of the supports of `f x`. -/
lemma support_lift_subset {Y Z : Type*}
    (f : Y → FreeAbelianGroup Z) (c : FreeAbelianGroup Y) :
    ((FreeAbelianGroup.lift f) c).support ⊆
      c.support.biUnion (fun x => (f x).support) := by
  rw [lift_eq_finsupp_sum]
  apply Finset.Subset.trans (support_finset_sum _ _)
  apply Finset.biUnion_mono
  intro x _ τ hτ
  by_cases hn : (FreeAbelianGroup.toFinsupp c) x = 0
  · simp [hn, FreeAbelianGroup.support_zero] at hτ
  · rwa [FreeAbelianGroup.support_zsmul _ hn] at hτ

open Classical in
/-- If a property `P` holds on the supports of `f x` for every `x` in the support of `c`,
then it holds on the support of `FreeAbelianGroup.lift f c`. -/
lemma lift_support_forall {Y Z : Type*} (f : Y → FreeAbelianGroup Z)
    (c : FreeAbelianGroup Y) (P : Z → Prop)
    (hP : ∀ x ∈ c.support, ∀ y ∈ (f x).support, P y) :
    ∀ y ∈ ((FreeAbelianGroup.lift f) c).support, P y := by
  intro y hy
  obtain ⟨x, hxc, hxf⟩ := Finset.mem_biUnion.mp (support_lift_subset f c hy)
  exact hP x hxc y hxf

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

/-- The barycentric subdivision vertex coordinates are nonnegative. -/
lemma barySubdivVertex_nonneg (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (k i : Fin (n + 1)) : 0 ≤ barySubdivVertex n π k i := by
  simp only [barySubdivVertex]; split <;> positivity

/-- The barycentric coordinates of any vertex of the barycentric subdivision sum to one,
exhibiting it as a point of the standard simplex. -/
lemma barySubdivVertex_sum (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    ∑ i : Fin (n + 1), barySubdivVertex n π k i = 1 := by
  simp only [barySubdivVertex]
  rw [← Finset.sum_filter]
  have hfilt : (Finset.univ.filter (fun i => ∃ j : Fin (n + 1), j ≤ k ∧ π j = i)) =
    (Finset.Iic k).image π := by
    ext i; simp [Finset.mem_filter, Finset.mem_image, Finset.mem_Iic]
  rw [hfilt, Finset.sum_const, Finset.card_image_of_injective _ π.injective, Fin.card_Iic]
  simp only [nsmul_eq_mul]
  push_cast
  field_simp

/-- The barycentric subdivision map sends a point of the standard simplex to a point of
the standard simplex. -/
lemma barySubdivMapFn_mem (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (t : Fin (n + 1) → ℝ) (ht : t ∈ stdSimplex ℝ (Fin (n + 1))) :
    barySubdivMapFn n π t ∈ stdSimplex ℝ (Fin (n + 1)) := by
  constructor
  · intro i
    apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg (ht.1 k) (barySubdivVertex_nonneg n π k i)
  · simp only [barySubdivMapFn]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, barySubdivVertex_sum, mul_one]
    exact ht.2

/-- The barycentric subdivision map is continuous, as a self-map of the standard simplex. -/
lemma barySubdivMap_continuous (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) :
    Continuous (fun (t : ↥(stdSimplex ℝ (Fin (n + 1)))) =>
      (⟨barySubdivMapFn n π t.1, barySubdivMapFn_mem n π t.1 t.2⟩ :
        ↥(stdSimplex ℝ (Fin (n + 1))))) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  simp only [barySubdivMapFn]
  apply continuous_finset_sum
  intro k _
  exact ((continuous_apply k).comp continuous_subtype_val).mul continuous_const

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

/-- The iterated subdivision operator is additive. -/
lemma iterateSubdivision_add {n : ℕ}
    (k : ℕ) (a b : SingularChains n X) :
    iterateSubdivision k (a + b) =
    iterateSubdivision k a + iterateSubdivision k b :=
  iterate_map_add (subdivisionOp n X) k a b

/-- Every singular simplex appearing in the support of `SingularChains.map σ c` has image
contained in the range of `σ`. -/
lemma range_subset_of_mem_support_map {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    {n : ℕ} (σ : C(Y, Z)) (c : SingularChains n Y)
    (τ : SingularSimplex n Z)
    (hτ : τ ∈ FreeAbelianGroup.support (SingularChains.map σ c)) :
    Set.range (show C(↥(stdSimplex ℝ (Fin (n + 1))), Z) from τ) ⊆ Set.range σ := by
  simp only [SingularChains.map] at hτ
  have hmap :
      τ ∈ ((FreeAbelianGroup.lift (FreeAbelianGroup.of ∘ SingularSimplex.map σ)) c).support :=
    hτ
  exact lift_support_forall (FreeAbelianGroup.of ∘ SingularSimplex.map σ) c
    (fun τ => Set.range (show C(↥(stdSimplex ℝ (Fin (n + 1))), Z) from τ) ⊆ Set.range σ)
    (fun ρ _ τ' hτ' => by
      simp only [Function.comp, FreeAbelianGroup.support_of, Finset.mem_singleton] at hτ'
      subst hτ'
      simp only [SingularSimplex.map]
      exact Set.range_comp_subset_range
        (show C(↥(stdSimplex ℝ (Fin (n + 1))), Y) from ρ) σ)
    τ hmap

/-- The subdivision operator preserves `𝒜`-smallness: if `c` is `𝒜`-small then so is
`$c`. -/
lemma isSmallChain_subdivisionOp {𝒜 : Set (Set X)} {n : ℕ} {c : SingularChains n X}
    (h : IsSmallChain 𝒜 c) :
    IsSmallChain 𝒜 (subdivisionOp n X c) := by
  intro τ hτ
  exact lift_support_forall
    (fun σ : SingularSimplex n X => SingularChains.map σ (stdSubdivisionChain n))
    c (fun τ => IsSmall 𝒜 τ)
    (fun σ hσ τ' hτ' => by
      obtain ⟨A, hA, hrange⟩ := h σ hσ
      exact ⟨A, hA, (range_subset_of_mem_support_map σ _ τ' hτ').trans hrange⟩)
    τ hτ

/-- If the `k`-th iterate of the subdivision operator applied to `c` is `𝒜`-small, then
so is the `(k+1)`-th iterate. -/
lemma isSmallChain_iterateSubdivision_succ {𝒜 : Set (Set X)} {n : ℕ}
    {c : SingularChains n X} {k : ℕ}
    (h : IsSmallChain 𝒜 (iterateSubdivision k c)) :
    IsSmallChain 𝒜 (iterateSubdivision (k + 1) c) := by
  show IsSmallChain 𝒜 ((⇑(subdivisionOp n X))^[k + 1] c)
  rw [Function.iterate_succ']
  exact isSmallChain_subdivisionOp h

/-- Monotonicity: once an iterate of the subdivision operator applied to `c` is
`𝒜`-small, all subsequent iterates remain `𝒜`-small. -/
lemma isSmallChain_iterateSubdivision_mono {𝒜 : Set (Set X)} {n : ℕ}
    {c : SingularChains n X} {k : ℕ}
    (h : IsSmallChain 𝒜 (iterateSubdivision k c)) (j : ℕ) :
    IsSmallChain 𝒜 (iterateSubdivision (k + j) c) := by
  induction j with
  | zero => rwa [Nat.add_zero]
  | succ j ih =>
    have : k + (j + 1) = (k + j) + 1 := by omega
    rw [this]
    exact isSmallChain_iterateSubdivision_succ ih
