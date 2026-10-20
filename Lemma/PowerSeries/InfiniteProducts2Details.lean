import Mathlib
import sympy.Basic
import sympy.series.formal.InfiniteProducts2Details
open PowerSeries
open scoped BigOperators PowerSeries


/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/InfiniteProducts2.lean)
-/
@[path]
private lemma essentiallyFinite_iff_support_finite
-- given
  (f : I → ℕ) :
-- imply
  PowerSeries.EssentiallyFinite f ↔ (Function.support f).Finite := by
-- proof
  apply PowerSeries.essentiallyFinite_iff_support_finite f

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/InfiniteProducts2.lean)
-/
@[path]
private lemma support_finite
-- given
  {f : I → ℕ}
  (hf : PowerSeries.EssentiallyFinite f) :
-- imply
  {i : I | f i ≠ 0}.Finite := by
-- proof
  apply PowerSeries.EssentiallyFinite.support_finite hf

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/InfiniteProducts2.lean)
-/
@[path]
private lemma essentiallyFinite_zero :
-- imply
  PowerSeries.EssentiallyFinite (fun _ : I => 0) := by
-- proof
  apply PowerSeries.essentiallyFinite_zero

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/InfiniteProducts2.lean)
-/
@[path]
private lemma essentiallyFinite_of_finite_support
-- given
  {f : I → ℕ}
  {s : Finset I}
  (hs : ∀ i, f i ≠ 0 → i ∈ s) :
-- imply
  PowerSeries.EssentiallyFinite f := by
-- proof
  apply PowerSeries.essentiallyFinite_of_finite_support hs

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/InfiniteProducts2.lean)
-/
@[path]
private lemma prodRule_claim3
  [CommRing K]
-- given
  (p : I → ℕ → PowerSeries K)
  (n : ℕ)
  (i : I)
  (k : ℕ)
  (hk : k ≠ 0)
  (hnotin : (i, k) ∉ CoeffSupportSetUnion p n) :
-- imply
  ∀ m ≤ n, coeff m (p i k) = 0 := by
-- proof
  apply PowerSeries.prodRule_claim3 p n i k hk hnotin

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/InfiniteProducts2.lean)
-/
@[path]
private lemma prodRule_claim4
  [CommRing K]
-- given
  (p : I → ℕ → PowerSeries K)
  (k : I → ℕ)
  (hp0 : ∀ i, p i 0 = 1)
  (hk : PowerSeries.EssentiallyFinite k) :
-- imply
  {i : I | p i (k i) ≠ 1}.Finite := by
-- proof
  apply PowerSeries.prodRule_claim4 p hp0 k hk

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/InfiniteProducts2.lean)
-/
@[path]
private lemma prodRule_claim5
  [CommRing K]
  [DecidableEq I]
-- given
  (p : I → ℕ → PowerSeries K)
  (n : ℕ)
  (k : I → ℕ)
  (j : I)
  (hk : PowerSeries.EssentiallyFinite k)
  (hp0 : ∀ i, p i 0 = 1)
  (hkj : k j ≠ 0)
  (hnotin : (j, k j) ∉ CoeffSupportSetUnion p n) :
-- imply
  ∀ s : Finset I, j ∈ s → coeff n (∏ i ∈ s, p i (k i)) = 0 := by
-- proof
  apply PowerSeries.prodRule_claim5 p n k hk hp0 j hkj hnotin

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/InfiniteProducts2.lean)
-/
@[path]
private lemma prodRule_claim6
  [CommRing K]
  [DecidableEq I]
-- given
  (p : I → ℕ → PowerSeries K)
  (n : ℕ)
  (k : I → ℕ)
  (j : I)
  (hk : PowerSeries.EssentiallyFinite k)
  (hp0 : ∀ i, p i 0 = 1)
  (hj_notin : j ∉ IndexSetIn p n)
  (hkj : k j ≠ 0) :
-- imply
  ∀ s : Finset I, j ∈ s → coeff n (∏ i ∈ s, p i (k i)) = 0 := by
-- proof
  apply PowerSeries.prodRule_claim6 p n k hk hp0 j hj_notin hkj

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/InfiniteProducts2.lean)
-/
@[path]
private lemma prodRule_claim7
  [CommRing K]
  [DecidableEq I]
-- given
  (p : I → ℕ → PowerSeries K)
  (n : ℕ)
  (hp0 : ∀ i, p i 0 = 1)
  (hTn_finite : (CoeffSupportSetUnion p n).Finite)
  (hIn_finite : (IndexSetIn p n).Finite)
  (hKn_finite : (ValueSetKn p n).Finite) :
-- imply
  {k : I → ℕ | PowerSeries.EssentiallyFinite k ∧ (∀ i ∉ hIn_finite.toFinset, k i = 0) ∧ coeff n (∏ i ∈ hIn_finite.toFinset, p i (k i)) ≠ 0}.Finite := by
-- proof
  apply PowerSeries.prodRule_claim7 p hp0 n hTn_finite hIn_finite hKn_finite

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/InfiniteProducts2.lean)
-/
@[path]
private lemma prodRule_claim8
  [CommRing K]
  [DecidableEq I]
-- given
  (p : I → ℕ → PowerSeries K)
  (n : ℕ)
  (In : Finset I)
  (S : I → Finset ℕ)
  (essFinFamilies : Finset (I → ℕ))
  (hp0 : ∀ i, p i 0 = 1)
  (hIn : ∀ i, i ∉ In → i ∉ IndexSetIn p n)
  (hS0 : ∀ i, 0 ∈ S i)
  (hEss : ∀ k ∈ essFinFamilies, PowerSeries.EssentiallyFinite k)
  (hSIn : ∀ k ∈ essFinFamilies, ∀ i ∉ In, k i = 0)
  (hValInS : ∀ k ∈ essFinFamilies, ∀ i ∈ In, k i ∈ S i)
  (hComplete : ∀ k, (∀ i ∉ In, k i = 0) → (∀ i ∈ In, k i ∈ S i) → k ∈ essFinFamilies) :
-- imply
  coeff n (∑ k ∈ essFinFamilies, ∏ i ∈ In, p i (k i)) = coeff n (∑ f ∈ Fintype.piFinset (fun i : In => S i.1), ∏ i : In, p i.1 (f i)) := by
-- proof
  apply PowerSeries.prodRule_claim8 p n hp0 In hIn S hS0 essFinFamilies hEss hSIn hValInS hComplete

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/InfiniteProducts2.lean)
-/
@[path]
private lemma prodRule_claim9
  [CommRing K]
-- given
  (p : I → ℕ → PowerSeries K)
  (n : ℕ)
  (i : I)
  (Si : Finset ℕ)
  (hi : i ∉ IndexSetIn p n)
  (hSi : 0 ∈ Si) :
-- imply
  ∀ m ≤ n, coeff m (∑ k ∈ Si \ {0}, p i k) = 0 := by
-- proof
  apply PowerSeries.prodRule_claim9 p n i hi Si hSi

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/InfiniteProducts2.lean)
-/
@[path]
private lemma prodRule_claim10
  [CommRing K]
  [DecidableEq I]
-- given
  (p : I → ℕ → PowerSeries K)
  (n : ℕ)
  (In : Finset I)
  (S : I → Finset ℕ)
  (J : Finset I)
  (hp0 : ∀ i, p i 0 = 1)
  (hIn : ∀ i, i ∉ In → i ∉ IndexSetIn p n)
  (hS0 : ∀ i, 0 ∈ S i)
  (hInJ : In ⊆ J) :
-- imply
  coeff n (∏ i ∈ J, ∑ k ∈ S i, p i k) = coeff n (∏ i ∈ In, ∑ k ∈ S i, p i k) := by
-- proof
  apply PowerSeries.prodRule_claim10 p n hp0 In hIn S hS0 J hInJ

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/InfiniteProducts2.lean)
-/
@[path]
private lemma prodRule_claim11
  [CommRing K]
  [DecidableEq I]
-- given
  (p : I → ℕ → PowerSeries K)
  (In : Finset I)
  (S : I → Finset ℕ) :
-- imply
  ∏ i ∈ In, ∑ k ∈ S i, p i k = ∑ f ∈ Fintype.piFinset (fun i : In => S i.1), ∏ i : In, p i.1 (f i) := by
-- proof
  apply PowerSeries.prodRule_claim11 p In S

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/InfiniteProducts2.lean)
-/
@[path]
private lemma prodRule_finite_interchange
  [CommRing K]
  [DecidableEq I]
-- given
  (p : I → ℕ → PowerSeries K)
  (M : Finset I)
  (S : I → Finset ℕ) :
-- imply
  ∏ i ∈ M, ∑ k ∈ S i, p i k = ∑ f ∈ Fintype.piFinset (fun i : M => S i.1), ∏ i : M, p i.1 (f i) := by
-- proof
  apply PowerSeries.prodRule_finite_interchange p M S

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/InfiniteProducts2.lean)
-/
@[path]
private lemma prodRule_infInf
  [CommRing K]
  [DecidableEq I]
-- given
  (p : I → ℕ → PowerSeries K)
  (S : I → Set ℕ)
  (hS0 : ∀ i, 0 ∈ S i)
  (hp0 : ∀ i, p i 0 = 1)
  (hSummable : ∀ m, {ik : I × ℕ | ik.2 ∈ S ik.1 ∧ ik.2 ≠ 0 ∧ coeff m (p ik.1 ik.2) ≠ 0}.Finite)
  (hMultipliable : ∀ n, ∃ M : Finset I, ∀ J : Finset I, M ⊆ J → ∀ Sfin : I → Finset ℕ, (∀ i, (Sfin i : Set ℕ) ⊆ S i) → (∀ i, 0 ∈ Sfin i) → coeff n (∏ i ∈ J, ∑ k ∈ Sfin i, p i k) = coeff n (∏ i ∈ M, ∑ k ∈ Sfin i, p i k)) :
-- imply
  ∀ n, ∃ M_n : Finset I, (∀ J : Finset I, M_n ⊆ J → ∀ Sfin : I → Finset ℕ, (∀ i, (Sfin i : Set ℕ) ⊆ S i) → (∀ i, 0 ∈ Sfin i) → coeff n (∏ i ∈ J, ∑ k ∈ Sfin i, p i k) = coeff n (∏ i ∈ M_n, ∑ k ∈ Sfin i, p i k)) ∧ (∀ Sfin : I → Finset ℕ, (∀ i, (Sfin i : Set ℕ) ⊆ S i) → (∀ i, 0 ∈ Sfin i) → coeff n (∏ i ∈ M_n, ∑ k ∈ Sfin i, p i k) = coeff n (∑ f ∈ Fintype.piFinset (fun i : M_n => Sfin i.1), ∏ i : M_n, p i.1 (f i))) := by
-- proof
  apply PowerSeries.prodRule_infInf p S hS0 hp0 hSummable hMultipliable

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/InfiniteProducts2.lean)
-/
@[path]
private lemma prodRule_infInf_coeff
  [CommRing K]
  [DecidableEq I]
-- given
  (p : I → ℕ → PowerSeries K)
  (n : ℕ)
  (M : Finset I)
  (Sfin : I → Finset ℕ) :
-- imply
  coeff n (∏ i ∈ M, ∑ k ∈ Sfin i, p i k) = coeff n (∑ f ∈ Fintype.piFinset (fun i : M => Sfin i.1), ∏ i : M, p i.1 (f i)) := by
-- proof
  apply PowerSeries.prodRule_infInf_coeff p n M Sfin

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/InfiniteProducts2.lean)
-/
@[path]
private lemma comp_prod_finite
  [CommRing K]
  [DecidableEq ι]
-- given
  (g : PowerSeries K)
  (hg : constantCoeff g = 0)
  (s : Finset ι)
  (f : ι → PowerSeries K) :
-- imply
  (∏ i ∈ s, f i).subst g = ∏ i ∈ s, (f i).subst g := by
-- proof
  apply PowerSeries.comp_prod_finite s f g hg

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/InfiniteProducts2.lean)
-/
@[path]
private lemma xnEquiv_comp
  [CommRing K]
-- given
  {n : ℕ}
  {f₁ f₂ g : PowerSeries K}
  (hf : ∀ k ≤ n, coeff k f₁ = coeff k f₂)
  (hg : constantCoeff g = 0) :
-- imply
  ∀ k ≤ n, coeff k (f₁.subst g) = coeff k (f₂.subst g) := by
-- proof
  apply PowerSeries.xnEquiv_comp hf hg

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/InfiniteProducts2.lean)
-/
@[path]
private lemma comp_prod_approx_determines
  [CommRing K]
  [DecidableEq I]
-- given
  (f : I → PowerSeries K)
  (g : PowerSeries K)
  (n : ℕ)
  (M : Finset I)
  (hg : constantCoeff g = 0)
  (hM_approx : ∀ k ≤ n, ∀ J : Finset I, M ⊆ J → coeff k (∏ i ∈ J, f i) = coeff k (∏ i ∈ M, f i)) :
-- imply
  ∀ J : Finset I, M ⊆ J → coeff n (∏ i ∈ J, (f i).subst g) = coeff n (∏ i ∈ M, (f i).subst g) := by
-- proof
  apply PowerSeries.comp_prod_approx_determines f g hg n M hM_approx

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/InfiniteProducts2.lean)
-/
@[path]
private lemma comp_prod_multipliable
  [CommRing K]
  [DecidableEq I]
-- given
  (f : I → PowerSeries K)
  (g : PowerSeries K)
  (hg : constantCoeff g = 0)
  (hf_mulable : ∀ n, ∃ M : Finset I, ∀ J : Finset I, M ⊆ J → coeff n (∏ i ∈ J, f i) = coeff n (∏ i ∈ M, f i)) :
-- imply
  ∀ n, ∃ M : Finset I, ∀ J : Finset I, M ⊆ J → coeff n (∏ i ∈ J, (f i).subst g) = coeff n (∏ i ∈ M, (f i).subst g) := by
-- proof
  apply PowerSeries.comp_prod_multipliable f g hg hf_mulable

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/InfiniteProducts2.lean)
-/
@[path]
private lemma comp_prod_infinite
  [CommRing K]
  [DecidableEq I]
-- given
  (f : I → PowerSeries K)
  (g prod_f : PowerSeries K)
  (hg : constantCoeff g = 0)
  (hf_mulable : ∀ n, ∃ M : Finset I, ∀ J : Finset I, M ⊆ J → coeff n (∏ i ∈ J, f i) = coeff n (∏ i ∈ M, f i))
  (hprod : ∀ n (M : Finset I), (∀ J : Finset I, M ⊆ J → coeff n (∏ i ∈ J, f i) = coeff n (∏ i ∈ M, f i)) → coeff n prod_f = coeff n (∏ i ∈ M, f i)) :
-- imply
  ∀ n, ∃ M : Finset I, coeff n (prod_f.subst g) = coeff n (∏ i ∈ M, (f i).subst g) := by
-- proof
  apply PowerSeries.comp_prod_infinite f g hg hf_mulable prod_f hprod

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/InfiniteProducts2.lean)
-/
@[path]
private lemma coeff_zero_of_dvd
  [CommRing K]
-- given
  {n : ℕ}
  {u v : PowerSeries K}
  (hdvd : u ∣ v)
  (hu : ∀ m ≤ n, coeff m u = 0) :
-- imply
  ∀ m ≤ n, coeff m v = 0 := by
-- proof
  apply PowerSeries.coeff_zero_of_dvd hdvd hu

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/InfiniteProducts2.lean)
-/
@[path]
private lemma coeff_mul_one_add_of_lt_order
  [CommRing K]
-- given
  {φ ψ : K⟦X⟧}
  (n : ℕ)
  (h : ↑n < ψ.order) :
-- imply
  coeff n (φ * (1 + ψ)) = coeff n φ := by
-- proof
  apply PowerSeries.coeff_mul_one_add_of_lt_order n h

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/InfiniteProducts2.lean)
-/
@[path]
private lemma coeff_prod_one_plus_summable
  [CommRing K]
  [DecidableEq I]
-- given
  (f : I → PowerSeries K)
  (n : ℕ)
  (hf_zero : ∀ i, ∀ m ≤ n, coeff m (f i) = 0)
  (a : PowerSeries K)
  (s : Finset I) :
-- imply
  ∀ m ≤ n, coeff m (a * ∏ i ∈ s, (1 + f i)) = coeff m a := by
-- proof
  apply PowerSeries.coeff_prod_one_plus_summable a f n hf_zero s


-- created on 2026-10-20
