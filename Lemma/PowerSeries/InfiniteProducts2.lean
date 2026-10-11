import Mathlib
import sympy.Basic
import sympy.series.formal.InfiniteProducts2
open scoped PowerSeries PowerSeries.WithPiTopology


/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_zero_eq
  [Zero M]
  (I : Type*) :
-- imply
  EssentiallyFinite (0 : I → M) := by
-- proof
  apply EssentiallyFinite.zero

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_finite_support_eq
  [Zero M]
  {f : I → M}
  (hf : EssentiallyFinite f) :
-- imply
  (Function.support f).Finite := by
-- proof
  apply EssentiallyFinite.finite_support hf

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_of_finite_eq
  [Zero M]
  [Finite I]
  (f : I → M) :
-- imply
  EssentiallyFinite f := by
-- proof
  apply EssentiallyFinite.of_finite f

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_of_fintype_eq
  [Zero M]
  [Fintype I]
  (f : I → M) :
-- imply
  EssentiallyFinite f := by
-- proof
  apply EssentiallyFinite.of_fintype f

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_subfamily_eq
  [Zero M]
  {f : I → M}
  (J : Set I)
  (hf : EssentiallyFinite f) :
-- imply
  EssentiallyFinite (fun i : J => f i) := by
-- proof
  apply EssentiallyFinite.subfamily J hf

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_const_zero_eq
  [Zero M] :
-- imply
  EssentiallyFinite (fun _ : I => (0 : M)) := by
-- proof
  apply EssentiallyFinite.const_zero

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_iff_eventually_cofinite_iff
  [Zero M]
  {f : I → M} :
-- imply
  EssentiallyFinite f ↔ ∀ᶠ i in Filter.cofinite, f i = 0 := by
-- proof
  apply EssentiallyFinite.iff_eventually_cofinite

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_iff_finite_set_of_ne_zero_iff
  [Zero M]
  {f : I → M} :
-- imply
  EssentiallyFinite f ↔ {i | f i ≠ 0}.Finite := by
-- proof
  apply EssentiallyFinite.iff_finite_setOf_ne_zero

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_iff_support_finite_iff
  [Zero M]
  {f : I → M} :
-- imply
  EssentiallyFinite f ↔ (Function.support f).Finite := by
-- proof
  apply EssentiallyFinite.iff_support_finite

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_neg_eq
  [AddGroup M]
  {f : I → M}
  (hf : EssentiallyFinite f) :
-- imply
  EssentiallyFinite (-f) := by
-- proof
  apply EssentiallyFinite.neg hf

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_add_eq
  [AddGroup M]
  {f g : I → M}
  (hf : EssentiallyFinite f)
  (hg : EssentiallyFinite g) :
-- imply
  EssentiallyFinite (f + g) := by
-- proof
  apply EssentiallyFinite.add hf hg

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_sub_eq
  [AddGroup M]
  {f g : I → M}
  (hf : EssentiallyFinite f)
  (hg : EssentiallyFinite g) :
-- imply
  EssentiallyFinite (f - g) := by
-- proof
  apply EssentiallyFinite.sub hf hg

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_mul_const_eq
  [Ring R]
  [NoZeroDivisors R]
  {f : I → R}
  (hf : EssentiallyFinite f)
  (c : R) :
-- imply
  EssentiallyFinite (fun i => f i * c) := by
-- proof
  apply EssentiallyFinite.mul_const hf c

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_const_mul_eq
  [Ring R]
  [NoZeroDivisors R]
  {f : I → R}
  (c : R)
  (hf : EssentiallyFinite f) :
-- imply
  EssentiallyFinite (fun i => c * f i) := by
-- proof
  apply EssentiallyFinite.const_mul c hf

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_to_finsupp_apply_eq
  [Zero M]
  {f : I → M}
  (hf : EssentiallyFinite f)
  (i : I) :
-- imply
  hf.toFinsupp i = f i := by
-- proof
  apply EssentiallyFinite.toFinsupp_apply hf i

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_mem_support_finset_iff
  [Zero M]
  {f : I → M}
  (hf : EssentiallyFinite f)
  (i : I) :
-- imply
  i ∈ hf.supportFinset ↔ f i ≠ 0 := by
-- proof
  apply EssentiallyFinite.mem_supportFinset_iff hf i

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_family_zero_apply_eq
  [Zero M]
  (i : I) :
-- imply
  (0 : EssentiallyFiniteFamily I M) i = 0 := by
-- proof
  apply EssentiallyFiniteFamily.zero_apply i

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_family_eventually_eq_zero_eq
  [Zero M]
  (f : EssentiallyFiniteFamily I M) :
-- imply
  ∀ᶠ i in Filter.cofinite, f i = 0 := by
-- proof
  apply EssentiallyFiniteFamily.eventually_eq_zero f

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_family_finite_support_eq
  [Zero M]
  (f : EssentiallyFiniteFamily I M) :
-- imply
  (Function.support f.val).Finite := by
-- proof
  apply EssentiallyFiniteFamily.finite_support f

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma prod_sum_eq_sum_prod_finset_eq
  [CommSemiring L]
  {n : ℕ}
  {m : Fin n → ℕ}
  (p : (i : Fin n) → Fin (m i) → L) :
-- imply
  ∏ i : Fin n, ∑ k : Fin (m i), p i k =
  ∑ f : (i : Fin n) → Fin (m i), ∏ i : Fin n, p i (f i) := by
-- proof
  apply prod_sum_eq_sum_prod_finset p

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma prod_sum_eq_sum_prod_finset'_eq
  [CommSemiring L]
  [Fintype N]
  [DecidableEq N]
  {S : N → Type*} [∀ i, Fintype (S i)]
  (p : (i : N) → S i → L) :
-- imply
  ∏ i : N, ∑ k : S i, p i k =
  ∑ f : (i : N) → S i, ∏ i : N, p i (f i) := by
-- proof
  apply prod_sum_eq_sum_prod_finset' p

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma summable_fin_prod_discrete_eq
  [CommRing K]
  [TopologicalSpace K]
  [DiscreteTopology K]
  {n : ℕ}
  {S : Fin n → Type*}
  (p : (i : Fin n) → S i → K⟦X⟧)
  (hp : ∀ i, Summable (p i)) :
-- imply
  Summable (fun f : (i : Fin n) → S i => ∏ i : Fin n, p i (f i)) := by
-- proof
  apply summable_finProd_discrete p hp

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma prod_tsum_eq_tsum_prod_finset_eq
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [DiscreteTopology K]
  {n : ℕ}
  {S : Fin n → Type*}
  (p : (i : Fin n) → S i → K⟦X⟧)
  (hp : ∀ i, Summable (p i)) :
-- imply
  ∏ i : Fin n, ∑' k, p i k =
  ∑' f : (i : Fin n) → S i, ∏ i : Fin n, p i (f i) := by
-- proof
  apply prod_tsum_eq_tsum_prod_finset p hp

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma prod_tsum_eq_tsum_prod_finset'_eq
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [DiscreteTopology K]
  [Fintype N]
  [DecidableEq N]
  {S : N → Type*}
  (p : (i : N) → S i → K⟦X⟧)
  (hp : ∀ i, Summable (p i)) :
-- imply
  ∏ i : N, ∑' k, p i k =
  ∑' f : (i : N) → S i, ∏ i : N, p i (f i) := by
-- proof
  apply prod_tsum_eq_tsum_prod_finset' p hp

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma prod_tsum_eq_tsum_prod_finset_discrete_eq
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [DiscreteTopology K]
  {n : ℕ}
  {S : Fin n → Type*}
  (p : (i : Fin n) → S i → K⟦X⟧)
  (hp : ∀ i, Summable (p i)) :
-- imply
  ∏ i : Fin n, ∑' k, p i k =
  ∑' f : (i : Fin n) → S i, ∏ i : Fin n, p i (f i) := by
-- proof
  apply prod_tsum_eq_tsum_prod_finset_discrete p hp

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma prod_tsum_eq_tsum_prod_finset'_discrete_eq
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [DiscreteTopology K]
  [Fintype N]
  [DecidableEq N]
  {S : N → Type*}
  (p : (i : N) → S i → K⟦X⟧)
  (hp : ∀ i, Summable (p i)) :
-- imply
  ∏ i : N, ∑' k, p i k =
  ∑' f : (i : N) → S i, ∏ i : N, p i (f i) := by
-- proof
  apply prod_tsum_eq_tsum_prod_finset'_discrete p hp

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma prod_finset_tsum_eq_tsum_prod_eq
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [DiscreteTopology K]
  [DecidableEq I]
  {S : I → Type*}
  (s : Finset I)
  (p : (i : I) → S i → K⟦X⟧)
  (hp : ∀ i ∈ s, Summable (p i)) :
-- imply
  ∏ i ∈ s, ∑' k : S i, p i k = ∑' f : (i : s) → S i, ∏ i : s, p i (f i) := by
-- proof
  apply prod_finset_tsum_eq_tsum_prod s p hp

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma tprod_tsum_eq_tsum_prod_essentially_finite_eq
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [DiscreteTopology K]
  {S : I → Type*} [∀ i, Zero (S i)] [∀ i, DecidableEq (S i)]
  (p : (i : I) → S i → K⟦X⟧)
  (hp_zero : ∀ i, p i 0 = 1)
  (hp_summable : Summable fun ik : (Σ i, Subtype (fun k : S i => k ≠ 0)) => p ik.1 ik.2.1) :
-- imply
  (tprod fun i : I => ∑' k : S i, p i k) =
  ∑' f : (Subtype fun f : (i : I) → S i => ∀ᶠ i in Filter.cofinite, f i = 0),
    (tprod fun i : I => p i (f.val i)) := by
-- proof
  apply tprod_tsum_eq_tsum_prod_essentiallyFinite p hp_zero hp_summable

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma tprod_tsum_eq_tsum_prod_essentially_finite_nat_eq
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [DiscreteTopology K]
  {S : PNat → Type*} [∀ i, Zero (S i)] [∀ i, DecidableEq (S i)]
  (p : (i : PNat) → S i → K⟦X⟧)
  (hp_zero : ∀ i, p i 0 = 1)
  (hp_summable : Summable fun ik : SBar S => p ik.1 ik.2.1) :
-- imply
  (tprod fun i : PNat => ∑' k : S i, p i k) =
  ∑' f : (Subtype fun f : (i : PNat) → S i => ∀ᶠ i in Filter.cofinite, f i = 0),
    (tprod fun i : PNat => p i (f.val i)) := by
-- proof
  apply tprod_tsum_eq_tsum_prod_essentiallyFinite_nat p hp_zero hp_summable

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma coeff_mul_tprod_one_add_eq_coeff_le
  [CommRing K]
  [TopologicalSpace K]
  [T2Space K]
  (a : K⟦X⟧)
  (f : J → K⟦X⟧)
  (hf_summable : Summable f)
  (n : ℕ)
  (hf_order : ∀ i : J, ∀ m ≤ n, (PowerSeries.coeff m) (f i) = 0) :
-- imply
  ∀ m ≤ n, (PowerSeries.coeff m) (a * (tprod fun i => (1 + f i))) =
  (PowerSeries.coeff m) a := by
-- proof
  apply coeff_mul_tprod_one_add_eq_coeff a f hf_summable n hf_order

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma euler_odd_parts_identity_eq
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [NoZeroDivisors K] :
-- imply
  (tprod fun i : PNat =>
    Ring.inverse (1 - (PowerSeries.X : K⟦X⟧) ^ (2 * (i : ℕ) - 1))) =
  (tprod fun k : PNat => (1 + (PowerSeries.X : K⟦X⟧) ^ (k : ℕ))) := by
-- proof
  apply euler_odd_parts_identity

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma euler_odd_parts_identity'_eq
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [NoZeroDivisors K] :
-- imply
  (tprod fun i : (Subtype fun n : PNat => Odd (n : ℕ)) =>
    Ring.inverse (1 - (PowerSeries.X : K⟦X⟧) ^ (i : ℕ))) =
  (tprod fun k : PNat => (1 + (PowerSeries.X : K⟦X⟧) ^ (k : ℕ))) := by
-- proof
  apply euler_odd_parts_identity'

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma euler_distinct_odd_partitions_eq
  (n : ℕ) :
-- imply
  numDistinctPartitions n = numOddPartitions n := by
-- proof
  apply euler_distinct_odd_partitions n

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma continuous_rescale_eq
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  (a : K) :
-- imply
  Continuous (PowerSeries.rescale a : K⟦X⟧ → K⟦X⟧) := by
-- proof
  apply continuous_rescale a

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma tprod_rescale_substitution_eq
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  (f : I → K⟦X⟧)
  (a : K)
  (hf : Multipliable f) :
-- imply
  PowerSeries.rescale a (tprod fun i => f i) =
  (tprod fun i => PowerSeries.rescale a (f i)) := by
-- proof
  apply tprod_rescale_substitution f a hf

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma binary_product_rule_eq
  [CommRing K]
  [TopologicalSpace K]
  [DiscreteTopology K]
  (a : ℕ → K⟦X⟧)
  (ha : Summable a) :
-- imply
  (tprod fun i : ℕ => (1 + a i)) =
  ∑' s : Finset ℕ, ∏ i ∈ s, a i := by
-- proof
  apply binary_product_rule a ha

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma binary_product_rule'_eq
  [CommRing K]
  [TopologicalSpace K]
  [DiscreteTopology K]
  (a : ℕ → K⟦X⟧)
  (ha : Summable a) :
-- imply
  (tprod fun i : ℕ => (1 + a i)) =
  ∑' J : (Subtype fun J : Set ℕ => J.Finite),
    (finprod fun i => (finprod fun (_ : i ∈ J.val) => a i)) := by
-- proof
  apply binary_product_rule' a ha


-- created on 2026-10-11
