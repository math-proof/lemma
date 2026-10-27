import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.GBSplittingUniqueness
open BigOperators GBUniqueness


namespace GBUniqueness

/--
[h0z_eq_cast](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingUniqueness.lean)
-/
@[path]
lemma h0z_eq_cast
  {s : Multiset ℤ}
  {m : ℤ} :
-- imply
  h0z s m = (h0_multiset s m : ℤ) := by
-- proof
  unfold h0z h0_multiset
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    rw [ih]; push_cast; ring

end GBUniqueness

namespace GBUniqueness

/--
[h0z_cons](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingUniqueness.lean)
-/
@[path]
lemma h0z_cons
  {a : ℤ}
  {s : Multiset ℤ}
  {m : ℤ} :
-- imply
  h0z (a ::ₘ s) m = ((a + m + 1).toNat : ℤ) + h0z s m := by
-- proof
  unfold h0z; simp [Multiset.map_cons, Multiset.sum_cons]

end GBUniqueness

namespace GBUniqueness

/--
[h0_multiset_cons](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingUniqueness.lean)
-/
@[path]
lemma h0_multiset_cons
  {a : ℤ}
  {s : Multiset ℤ}
  {m : ℤ} :
-- imply
  h0_multiset (a ::ₘ s) m = (a + m + 1).toNat + h0_multiset s m := by
-- proof
  unfold h0_multiset; simp [Multiset.map_cons, Multiset.sum_cons]

end GBUniqueness

namespace GBUniqueness

/--
[single_second_diff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingUniqueness.lean)
-/
@[path]
lemma single_second_diff
  {d' d : ℤ} :
-- imply
  ((d' - d + 1).toNat : ℤ) - 2 * (d' - d).toNat + (d' - d - 1).toNat = if d' = d then 1 else 0 := by
-- proof
  split_ifs with h
  · subst h; simp
  · by_cases h1 : d < d'
    ·
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ d' - d - 1),
        Int.toNat_of_nonneg (by omega : 0 ≤ d' - d),
        Int.toNat_of_nonneg (by omega : 0 ≤ d' - d + 1)]
      ring
    ·
      simp [Int.toNat_eq_zero.mpr (by omega : d' - d + 1 ≤ 0),
        Int.toNat_eq_zero.mpr (by omega : d' - d ≤ 0),
        Int.toNat_eq_zero.mpr (by omega : d' - d - 1 ≤ 0)]

end GBUniqueness

namespace GBUniqueness

/--
[second_diff_eq_count](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingUniqueness.lean)
-/
@[path]
lemma second_diff_eq_count
  {s : Multiset ℤ}
  {d : ℤ} :
-- imply
  h0z s (-d) - 2 * h0z s (-d - 1) + h0z s (-d - 2) = s.count d := by
-- proof
  induction s using Multiset.induction with
  | empty => simp [h0z]
  | cons a s ih =>
    rw [h0z_cons, h0z_cons, h0z_cons, Multiset.count_cons]
    have eq1 : a + (-d) + 1 = a - d + 1 := by ring
    have eq2 : a + (-d - 1) + 1 = a - d := by ring
    have eq3 : a + (-d - 2) + 1 = a - d - 1 := by ring
    rw [eq1, eq2, eq3]
    push_cast
    linarith [single_second_diff a d,
      show (if a = d then (1 : ℤ) else 0) = if d = a then 1 else 0 from
        by split_ifs <;> omega]

end GBUniqueness

namespace GBUniqueness

/--
[h0z_determines_multiset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingUniqueness.lean)
-/
@[path]
lemma h0z_determines_multiset
  {s t : Multiset ℤ}
-- given
  (h : ∀ m : ℤ, h0z s m = h0z t m) :
-- imply
  s = t := by
-- proof
  ext d
  have hs := second_diff_eq_count s d
  have ht := second_diff_eq_count t d
  rw [h (-d), h (-d - 1), h (-d - 2)] at hs
  exact_mod_cast hs.symm.trans ht

end GBUniqueness

namespace GBUniqueness

/--
[h0_multiset_determines_multiset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingUniqueness.lean)
-/
@[path]
lemma h0_multiset_determines_multiset
  {s t : Multiset ℤ}
-- given
  (h : ∀ m : ℤ, h0_multiset s m = h0_multiset t m) :
-- imply
  s = t := by
-- proof
  apply h0z_determines_multiset
  intro m
  rw [h0z_eq_cast, h0z_eq_cast]
  exact_mod_cast h m

end GBUniqueness

namespace GBUniqueness

/--
[h0_twisted_eq_h0_multiset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingUniqueness.lean)
-/
@[path]
lemma h0_twisted_eq_h0_multiset
  {n : ℕ}
  {s : GBExistence.SplittingType n}
  {t : ℤ} :
-- imply
  s.h0_twisted t = h0_multiset (degreesToMultiset s.degrees) t := by
-- proof
  unfold GBExistence.SplittingType.h0_twisted GBExistence.h0_dim
  unfold h0_multiset degreesToMultiset
  rw [Multiset.map_map, ← Finset.sum_eq_multiset_sum]
  rfl

end GBUniqueness

namespace GBUniqueness

/--
[splitting_uniqueness_multiset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingUniqueness.lean)
-/
@[path]
lemma splitting_uniqueness_multiset
  {n : ℕ}
  {s₁ s₂ : GBExistence.SplittingType n}
-- given
  (h : ∀ t : ℤ, s₁.h0_twisted t = s₂.h0_twisted t) :
-- imply
  degreesToMultiset s₁.degrees = degreesToMultiset s₂.degrees := by
-- proof
  apply h0_multiset_determines_multiset
  intro m
  rw [← h0_twisted_eq_h0_multiset, ← h0_twisted_eq_h0_multiset]
  exact h m

end GBUniqueness

namespace GBUniqueness

/--
[sorted_eq_of_multiset_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingUniqueness.lean)
-/
@[path]
lemma sorted_eq_of_multiset_eq
  {n : ℕ}
  {f g : Fin n → ℤ}
-- given
  (hf : ∀ i j : Fin n, i ≤ j → g j ≤ g i)
  (hg : ∀ i j : Fin n, i ≤ j → f j ≤ f i)
  (hmulti : degreesToMultiset f = degreesToMultiset g) :
-- imply
  f = g := by
-- proof
  have hperm : (List.ofFn f).Perm (List.ofFn g) := by
    rw [← Multiset.coe_eq_coe]
    show (List.ofFn f : Multiset ℤ) = (List.ofFn g : Multiset ℤ)
    unfold degreesToMultiset at hmulti
    rwa [Fin.univ_val_map, Fin.univ_val_map] at hmulti
  have hsorted_f : (List.ofFn f).Pairwise (· ≥ ·) := by
    rw [List.pairwise_ofFn]
    intro i j hij
    exact hg i j (le_of_lt hij)
  have hsorted_g : (List.ofFn g).Pairwise (· ≥ ·) := by
    rw [List.pairwise_ofFn]
    intro i j hij
    exact hf i j (le_of_lt hij)
  have hlist_eq : List.ofFn f = List.ofFn g :=
    hperm.eq_of_pairwise
      (fun a b _ _ (h1 : a ≥ b) (h2 : b ≥ a) => le_antisymm h2 h1)
      hsorted_f hsorted_g
  exact List.ofFn_injective hlist_eq

end GBUniqueness

namespace GBUniqueness

/--
[splitting_uniqueness_sorted](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingUniqueness.lean)
-/
@[path]
lemma splitting_uniqueness_sorted
  {n : ℕ}
  {s₁ s₂ : GBExistence.SplittingType n}
-- given
  (h : ∀ t : ℤ, s₁.h0_twisted t = s₂.h0_twisted t) :
-- imply
  s₁.degrees = s₂.degrees := by
-- proof
  exact sorted_eq_of_multiset_eq s₁.degrees s₂.degrees
    s₂.sorted s₁.sorted
    (splitting_uniqueness_multiset s₁ s₂ h)

end GBUniqueness

namespace GBUniqueness

/--
[h0_directsum_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingUniqueness.lean)
-/
@[path]
lemma h0_directsum_formula
  {n : ℕ}
  {degrees : Fin n → ℤ}
  {m : ℤ} :
-- imply
  ∑ i, GBExistence.h0_dim (degrees i + m) = h0_multiset (degreesToMultiset degrees) m := by
-- proof
  unfold GBExistence.h0_dim h0_multiset degreesToMultiset
  rw [Multiset.map_map, ← Finset.sum_eq_multiset_sum]
  rfl

end GBUniqueness

namespace GBUniqueness

/--
[h1_directsum_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingUniqueness.lean)
-/
@[path]
lemma h1_directsum_formula
  {n : ℕ}
  {degrees : Fin n → ℤ}
  {m : ℤ} :
-- imply
  ∑ i, GBExistence.h1_dim (degrees i + m) = h1_multiset (degreesToMultiset degrees) m := by
-- proof
  unfold GBExistence.h1_dim h1_multiset degreesToMultiset
  rw [Multiset.map_map, ← Finset.sum_eq_multiset_sum]
  congr 1; ext d; simp [Function.comp]; ring_nf

end GBUniqueness

namespace GBUniqueness

/--
[second_diff_eq_count_nat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingUniqueness.lean)
-/
@[path]
lemma second_diff_eq_count_nat
  {s : Multiset ℤ}
  {d : ℤ} :
-- imply
  h0_multiset s (-d) + h0_multiset s (-d - 2) - 2 * h0_multiset s (-d - 1) = s.count d := by
-- proof
  have hz := second_diff_eq_count s d
  rw [h0z_eq_cast, h0z_eq_cast, h0z_eq_cast] at hz
  omega

end GBUniqueness


-- created on 2026-10-23
