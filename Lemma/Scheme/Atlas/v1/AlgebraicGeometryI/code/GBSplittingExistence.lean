import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.GBSplittingExistence.Part2
open BigOperators GBExistence


namespace GBExistence

/--
[h1_dim_of_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingExistence.lean)
-/
@[path]
lemma h1_dim_of_nonneg
  {d : ℤ}
-- given
  (hd : 0 ≤ d) :
-- imply
  h1_dim d = 0 := by
-- proof
  unfold h1_dim; rw [Int.toNat_eq_zero]; omega

end GBExistence

namespace GBExistence

/--
[h0_dim_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingExistence.lean)
-/
@[path]
lemma h0_dim_neg
  {d : ℤ}
-- given
  (hd : d < -1) :
-- imply
  h0_dim d = 0 := by
-- proof
  unfold h0_dim; rw [Int.toNat_eq_zero]; omega

end GBExistence

namespace GBExistence

/--
[h0_dim_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingExistence.lean)
-/
@[path]
lemma h0_dim_nonpos
  {d : ℤ}
-- given
  (hd : d ≤ -1) :
-- imply
  h0_dim d = 0 := by
-- proof
  unfold h0_dim; rw [Int.toNat_eq_zero]; omega

end GBExistence

namespace GBExistence

/--
[h0_dim_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingExistence.lean)
-/
@[path]
lemma h0_dim_pos
  {d : ℤ}
-- given
  (hd : 0 ≤ d) :
-- imply
  0 < h0_dim d := by
-- proof
  unfold h0_dim
  have : (d + 1).toNat ≠ 0 := by
    intro h; have := Int.toNat_eq_zero.mp h; omega
  omega

end GBExistence

namespace GBExistence

/--
[euler_char_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingExistence.lean)
-/
@[path]
lemma euler_char_formula
  {d : ℤ} :
-- imply
  (h0_dim d : ℤ) - (h1_dim d : ℤ) = d + 1 := by
-- proof
  unfold h0_dim h1_dim
  by_cases hd : 0 ≤ d + 1
  · have h1 : (d + 1).toNat = (d + 1).toNat := rfl
    have h2 : (-d - 1).toNat = 0 := by rw [Int.toNat_eq_zero]; omega
    rw [h2]; push_cast; rw [Int.toNat_of_nonneg hd]; omega
  · push Not at hd
    have h1 : (d + 1).toNat = 0 := by rw [Int.toNat_eq_zero]; omega
    rw [h1]; push_cast
    rw [Int.toNat_of_nonneg (show 0 ≤ -d - 1 by omega)]
    omega

end GBExistence

namespace GBExistence

/--
[h1_vanishes_ge_neg1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingExistence.lean)
-/
@[path]
lemma h1_vanishes_ge_neg1
  {d : ℤ}
-- given
  (hd : -1 ≤ d) :
-- imply
  h1_dim d = 0 := by
-- proof
  unfold h1_dim; rw [Int.toNat_eq_zero]; omega

end GBExistence

namespace GBExistence

/--
[ext1_dim_zero_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingExistence.lean)
-/
@[path]
lemma ext1_dim_zero_of_le
  {a b : ℤ}
-- given
  (h : a ≤ b) :
-- imply
  ext1_dim a b = 0 := by
-- proof
  unfold ext1_dim; exact h1_vanishes_ge_neg1 (by omega)

end GBExistence

namespace GBExistence

/--
[pid_torsionFree_free](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingExistence.lean)
-/
@[path]
lemma pid_torsionFree_free
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsPrincipalIdealRing R]
  {M : Type*}
  [AddCommGroup M]
  [Module R M]
  [Module.Finite R M]
  [Module.IsTorsionFree R M] :
-- imply
  Module.Free R M :=
-- proof
  inferInstance

end GBExistence

namespace GBExistence

/--
[SplittingType.le_maxDegree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingExistence.lean)
-/
@[path]
lemma SplittingType.le_maxDegree
  {n : ℕ}
  {s : SplittingType (n + 1)}
  {i : Fin (n + 1)} :
-- imply
  s.degrees i ≤ s.maxDegree :=
-- proof
  s.sorted ⟨0, Nat.zero_lt_succ n⟩ i (Fin.zero_le i)

end GBExistence

namespace GBExistence

/--
[h0_split_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingExistence.lean)
-/
@[path]
lemma h0_split_decomp
  {n : ℕ}
  {s : SplittingType (n + 1)}
  {t : ℤ} :
-- imply
  s.h0_twisted t = h0_dim (s.maxDegree + t) + s.tail.h0_twisted t := by
-- proof
  simp only [SplittingType.h0_twisted, SplittingType.tail, SplittingType.maxDegree,
    Fin.sum_univ_succ]; rfl

end GBExistence

namespace GBExistence

/--
[h1_split_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingExistence.lean)
-/
@[path]
lemma h1_split_decomp
  {n : ℕ}
  {s : SplittingType (n + 1)}
  {t : ℤ} :
-- imply
  s.h1_twisted t = h1_dim (s.maxDegree + t) + s.tail.h1_twisted t := by
-- proof
  simp only [SplittingType.h1_twisted, SplittingType.tail, SplittingType.maxDegree,
    Fin.sum_univ_succ]; rfl

end GBExistence

namespace GBExistence

/--
[inductive_ext1_vanishing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingExistence.lean)
-/
@[path]
lemma inductive_ext1_vanishing
  {n : ℕ}
  {s : SplittingType (n + 1)} :
-- imply
  ∑ i : Fin n, ext1_dim (s.tail.degrees i) s.maxDegree = 0 := by
-- proof
  apply Finset.sum_eq_zero
  intro i _
  apply ext1_dim_zero_of_le
  exact s.le_maxDegree (Fin.succ i)

end GBExistence

namespace GBExistence

/--
[degrees_le_zero_of_h0_twist_vanish](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingExistence.lean)
-/
@[path]
lemma degrees_le_zero_of_h0_twist_vanish
  {n : ℕ}
  {degrees : Fin n → ℤ}
-- given
  (h : h0_total (fun i => degrees i - 1) = 0) :
-- imply
  ∀ i, degrees i ≤ 0 := by
-- proof
  intro i
  by_contra h_pos
  push Not at h_pos
  have h1 : 0 < h0_dim (degrees i - 1) := h0_dim_pos (by omega)
  have h2 : h0_dim (degrees i - 1) ≤ h0_total (fun j => degrees j - 1) := by
    unfold h0_total
    exact Finset.single_le_sum (f := fun j => h0_dim (degrees j - 1))
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

end GBExistence

namespace GBExistence

/--
[split_riemann_roch](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingExistence.lean)
-/
@[path]
lemma split_riemann_roch
  {n : ℕ}
  {s : SplittingType n}
  {t : ℤ} :
-- imply
  (s.h0_twisted t : ℤ) - (s.h1_twisted t : ℤ) = ∑ i, (s.degrees i + t + 1) := by
-- proof
  unfold SplittingType.h0_twisted SplittingType.h1_twisted
  push_cast
  rw [← Finset.sum_sub_distrib]
  congr 1; ext i
  exact euler_char_formula (s.degrees i + t)

end GBExistence

namespace GBExistence

/--
[split_total_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingExistence.lean)
-/
@[path]
lemma split_total_degree
  {n : ℕ}
  {s : SplittingType n} :
-- imply
  (s.h0_twisted 0 : ℤ) - (s.h1_twisted 0 : ℤ) = (∑ i, s.degrees i) + n := by
-- proof
  rw [split_riemann_roch]
  simp [Finset.sum_add_distrib, Finset.sum_const]

end GBExistence

namespace GBExistence

/--
[split_euler_additive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingExistence.lean)
-/
@[path]
lemma split_euler_additive
  {n : ℕ}
  {s : SplittingType (n + 1)}
  {t : ℤ} :
-- imply
  (s.h0_twisted t : ℤ) - (s.h1_twisted t : ℤ) = ((h0_dim (s.maxDegree + t) : ℤ) - (h1_dim (s.maxDegree + t) : ℤ)) + ((s.tail.h0_twisted t : ℤ) - (s.tail.h1_twisted t : ℤ)) := by
-- proof
  rw [h0_split_decomp, h1_split_decomp]
  push_cast; ring

end GBExistence

namespace GBExistence

/--
[normalized_has_section](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingExistence.lean)
-/
@[path]
lemma normalized_has_section
  {n : ℕ}
  {s : SplittingType (n + 1)}
-- given
  (h_max : s.maxDegree = 0) :
-- imply
  0 < s.h0_twisted 0 := by
-- proof
  unfold SplittingType.h0_twisted
  set a0 : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
  have h1 : 0 < h0_dim (s.degrees a0 + 0) := by
    simp [show s.degrees a0 = 0 from h_max]; exact h0_dim_pos le_rfl
  have h2 : h0_dim (s.degrees a0 + 0) ≤ ∑ i, h0_dim (s.degrees i + 0) :=
    Finset.single_le_sum (f := fun i => h0_dim (s.degrees i + 0))
      (fun j _ => Nat.zero_le _) (Finset.mem_univ a0)
  linarith

end GBExistence

namespace GBExistence

/--
[h0_dim_matches_cohomology](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingExistence.lean)
-/
@[path]
lemma h0_dim_matches_cohomology
  {k : Type}
  [Field k]
  {d : ℤ}
-- given
  (hd : 0 ≤ d) :
-- imply
  (h0_dim d : ℕ) = Module.finrank k (SheafCohomology.H0 k d) := by
-- proof
  rw [SheafCohomology.finrank_H0_of_nonneg k d hd]; rfl

end GBExistence

namespace GBExistence

/--
[h0_dim_matches_cohomology_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingExistence.lean)
-/
@[path]
lemma h0_dim_matches_cohomology_neg
  {k : Type}
  [Field k]
  {d : ℤ}
-- given
  (hd : d < 0) :
-- imply
  (h0_dim d : ℕ) = Module.finrank k (SheafCohomology.H0 k d) := by
-- proof
  rw [SheafCohomology.finrank_H0_of_neg k d hd, h0_dim_nonpos (by omega)]

end GBExistence

namespace GBExistence

/--
[h1_dim_matches_cohomology](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingExistence.lean)
-/
@[path]
lemma h1_dim_matches_cohomology
  {k : Type}
  [Field k]
  {d : ℤ}
-- given
  (hd : 0 ≤ d) :
-- imply
  (h1_dim d : ℕ) = Module.finrank k (SheafCohomology.H1 k d) := by
-- proof
  rw [SheafCohomology.finrank_H1_of_nonneg k d hd, h1_dim_of_nonneg hd]

end GBExistence

namespace GBExistence

/--
[h1_dim_matches_cohomology_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingExistence.lean)
-/
@[path]
lemma h1_dim_matches_cohomology_neg
  {k : Type}
  [Field k]
  {d : ℤ}
-- given
  (hd : d < 0) :
-- imply
  (h1_dim d : ℕ) = Module.finrank k (SheafCohomology.H1 k d) := by
-- proof
  rw [SheafCohomology.finrank_H1_of_neg k d hd]; rfl

end GBExistence


-- created on 2026-10-23
