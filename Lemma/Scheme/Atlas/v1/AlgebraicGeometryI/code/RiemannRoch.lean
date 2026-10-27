import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannRoch
open CohomologyP1 RiemannRoch


namespace RiemannRoch

/--
[dimH0_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRoch.lean)
-/
@[path]
lemma dimH0_nonneg
  {k : Type}
  [Field k]
  {m : ℕ} :
-- imply
  dimH0 k ↑m = m + 1 :=
-- proof
  finrank_H0_nonneg k m

end RiemannRoch

namespace RiemannRoch

/--
[dimH0_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRoch.lean)
-/
@[path]
lemma dimH0_neg
  {k : Type}
  [Field k]
  {n : ℤ}
-- given
  (hn : n < 0) :
-- imply
  dimH0 k n = 0 := by
-- proof
  unfold dimH0
  rw [H0_vanishes_neg k n hn]
  exact finrank_bot k (ℤ →₀ k)

end RiemannRoch

namespace RiemannRoch

/--
[dimH1_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRoch.lean)
-/
@[path]
lemma dimH1_nonneg
  {k : Type}
  [Field k]
  {m : ℕ} :
-- imply
  dimH1 k ↑m = 0 :=
-- proof
  finrank_H1_nonneg k m

end RiemannRoch

namespace RiemannRoch

/--
[dimH1_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRoch.lean)
-/
@[path]
lemma dimH1_neg
  {k : Type}
  [Field k]
  {n : ℤ}
-- given
  (hn : n < 0) :
-- imply
  dimH1 k n = (-n - 1).toNat :=
-- proof
  finrank_H1_neg k n hn

end RiemannRoch

namespace RiemannRoch

/--
[serre_duality_P1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRoch.lean)
-/
@[path]
lemma serre_duality_P1
  {k : Type}
  [Field k]
  {n : ℤ} :
-- imply
  dimH1 k n = dimH0 k (-2 - n) := by
-- proof
  by_cases hn : 0 ≤ n
  ·
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [dimH1_nonneg, dimH0_neg k (-2 - ↑m) (by omega)]
  · push Not at hn
    by_cases hn2 : n = -1
    ·
      subst hn2
      rw [dimH1_neg k (-1) (by norm_num)]
      simp
      rw [dimH0_neg k (-1) (by norm_num)]
    ·
      have hn_le : n ≤ -2 := by omega
      have h_nn : 0 ≤ -2 - n := by omega
      rw [dimH1_neg k n hn]
      obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le h_nn
      rw [hm, dimH0_nonneg]
      zify [show 0 ≤ -n - 1 by omega]
      rw [← hm]
      omega

end RiemannRoch

namespace RiemannRoch

/--
[riemann_roch_P1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRoch.lean)
-/
@[path]
lemma riemann_roch_P1
  {k : Type}
  [Field k]
  {d : ℤ} :
-- imply
  (dimH0 k d : ℤ) - (dimH1 k d : ℤ) = d + 1 := by
-- proof
  by_cases hd : 0 ≤ d
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hd
    rw [dimH0_nonneg, dimH1_nonneg]
    push_cast
    ring
  · push Not at hd
    rw [dimH0_neg k d hd, dimH1_neg k d hd]
    push_cast
    rw [Int.toNat_of_nonneg (show 0 ≤ -d - 1 by omega)]
    omega

end RiemannRoch

namespace RiemannRoch

/--
[canonical_bundle_P1_H0](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRoch.lean)
-/
@[path]
lemma canonical_bundle_P1_H0
  {k : Type}
  [Field k] :
-- imply
  dimH0 k (-2) = 0 :=
-- proof
  dimH0_neg k (-2) (by norm_num)

end RiemannRoch

namespace RiemannRoch

/--
[canonical_bundle_P1_H1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRoch.lean)
-/
@[path]
lemma canonical_bundle_P1_H1
  {k : Type}
  [Field k] :
-- imply
  dimH1 k (-2) = 1 := by
-- proof
  rw [dimH1_neg k (-2) (by norm_num)]
  norm_num

end RiemannRoch

namespace RiemannRoch

/--
[genus_line](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRoch.lean)
-/
@[path]
lemma genus_line
  {k : Type}
  [Field k] :
-- imply
  genus 1 = 0 := by
-- proof
decide

end RiemannRoch

namespace RiemannRoch

/--
[genus_conic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRoch.lean)
-/
@[path]
lemma genus_conic
  {k : Type}
  [Field k] :
-- imply
  genus 2 = 0 := by
-- proof
decide

end RiemannRoch

namespace RiemannRoch

/--
[genus_cubic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRoch.lean)
-/
@[path]
lemma genus_cubic
  {k : Type}
  [Field k] :
-- imply
  genus 3 = 1 := by
-- proof
decide

end RiemannRoch

namespace RiemannRoch

/--
[genus_quartic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRoch.lean)
-/
@[path]
lemma genus_quartic
  {k : Type}
  [Field k] :
-- imply
  genus 4 = 3 := by
-- proof
decide

end RiemannRoch

namespace RiemannRoch

/--
[adjunction_formula_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRoch.lean)
-/
@[path]
lemma adjunction_formula_nonneg
  {k : Type}
  [Field k]
  {d : ℕ} :
-- imply
  d * (d - 3) = 2 * genus d - 2 := by
-- proof
  unfold genus
  by_cases hd : d ≤ 4
  · interval_cases d <;> simp
  · push Not at hd
    have h_even : 2 ∣ (d - 1) * (d - 2) := by
      obtain ⟨k, hk⟩ | ⟨k, hk⟩ := Nat.even_or_odd (d - 1)
      · exact ⟨k * (d - 2), by rw [hk]; ring⟩
      · have hd2 : d - 2 = 2 * k := by omega
        exact ⟨(d - 1) * k, by rw [hd2]; ring⟩
    rw [Nat.mul_div_cancel' h_even]
    have h_ge : 2 ≤ (d - 1) * (d - 2) :=
      Nat.le_trans (by norm_num : 2 ≤ 4 * 3) (Nat.mul_le_mul (by omega) (by omega))
    zify [show 3 ≤ d by omega, show 1 ≤ d by omega, show 2 ≤ d by omega, h_ge]
    ring

end RiemannRoch

namespace RiemannRoch

/--
[adjunction_formula_alt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRoch.lean)
-/
@[path]
lemma adjunction_formula_alt
  {k : Type}
  [Field k]
  {d : ℕ}
-- given
  (hd : 3 ≤ d) :
-- imply
  d * (d - 3) + 2 = (d - 1) * (d - 2) := by
-- proof
  zify [hd, show 1 ≤ d by omega, show 2 ≤ d by omega]
  ring

end RiemannRoch

namespace RiemannRoch

/--
[euler_char_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRoch.lean)
-/
@[path]
lemma euler_char_eq
  {k : Type}
  [Field k]
  {n : ℤ} :
-- imply
  euler_char k n = n + 1 :=
-- proof
  riemann_roch_P1 k n

end RiemannRoch

namespace RiemannRoch

/--
[euler_char_structure_sheaf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRoch.lean)
-/
@[path]
lemma euler_char_structure_sheaf
  {k : Type}
  [Field k] :
-- imply
  euler_char k 0 = 1 := by
-- proof
  rw [euler_char_eq]; ring

end RiemannRoch

namespace RiemannRoch

/--
[riemann_roch_serre_form](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRoch.lean)
-/
@[path]
lemma riemann_roch_serre_form
  {k : Type}
  [Field k]
  {d : ℤ} :
-- imply
  (dimH0 k d : ℤ) - (dimH0 k (-2 - d) : ℤ) = d + 1 := by
-- proof
  have h := riemann_roch_P1 k d
  have h2 := serre_duality_P1 k d
  rwa [show (dimH1 k d : ℤ) = (dimH0 k (-2 - d) : ℤ) from congrArg _ h2] at h

end RiemannRoch

namespace RiemannRoch

/--
[genus_line_eq_dimH1_P1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRoch.lean)
-/
@[path]
lemma genus_line_eq_dimH1_P1
  {k : Type}
  [Field k] :
-- imply
  (genus 1 : ℤ) = (dimH1 k (0 : ℤ) : ℤ) := by
-- proof
  rw [genus_line, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, dimH1_nonneg]

end RiemannRoch

namespace RiemannRoch

/--
[genus_line_euler_consistency](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRoch.lean)
-/
@[path]
lemma genus_line_euler_consistency
  {k : Type}
  [Field k] :
-- imply
  euler_char k 0 = 1 - (genus 1 : ℤ) := by
-- proof
  rw [euler_char_eq, genus_line]; ring

end RiemannRoch


-- created on 2026-10-23
