import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.DifferentialAnalysis.code.SchwartzSeminormsFix
open SchwartzSeminorms
open scoped SchwartzMap


namespace SchwartzSeminorms

/--
[weighted_norm_le_sup_seminorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminormsFix.lean)
-/
@[path]
lemma weighted_norm_le_sup_seminorm
  {K : ℕ}
  {k n : ℕ}
  {f : 𝓢(E, F)}
  {x : E}
-- given
  (hk : k ≤ K)
  (hn : n ≤ K) :
-- imply
  (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ 2 ^ K * (Finset.Iic (K, K)).sup (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2) f :=
-- proof
  SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := 𝕜) (m := (K, K)) hk hn f x

end SchwartzSeminorms

namespace SchwartzSeminorms

/--
[monomial_norm_le_weighted_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminormsFix.lean)
-/
@[path]
lemma monomial_norm_le_weighted_norm
  {k n : ℕ}
  {f : 𝓢(E, F)}
  {x : E} :
-- imply
  ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ n (⇑f) x‖ := by
-- proof
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact pow_le_pow_left₀ (norm_nonneg x) (le_add_of_nonneg_left zero_le_one) k

end SchwartzSeminorms

namespace SchwartzSeminorms

/--
[seminorm_le_two_pow_mul_sup_seminorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminormsFix.lean)
-/
@[path]
lemma seminorm_le_two_pow_mul_sup_seminorm
  {K : ℕ}
  {k n : ℕ}
  {f : 𝓢(E, F)}
-- given
  (hk : k ≤ K)
  (hn : n ≤ K) :
-- imply
  SchwartzMap.seminorm 𝕜 k n f ≤ 2 ^ K * (Finset.Iic (K, K)).sup (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2) f := by
-- proof
  apply SchwartzMap.seminorm_le_bound 𝕜 k n f
  · positivity
  · intro x
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑f) x‖
      ≤ (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ n (⇑f) x‖ :=
        monomial_norm_le_weighted_norm k n f x
      _ ≤ 2 ^ K * ((Finset.Iic (K, K)).sup
        (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2)) f :=
        weighted_norm_le_sup_seminorm hk hn f x

end SchwartzSeminorms

namespace SchwartzSeminorms

/--
[individual_le_sup_seminorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminormsFix.lean)
-/
@[path]
lemma individual_le_sup_seminorm
  {K : ℕ}
  {k n : ℕ}
  {f : 𝓢(E, F)}
-- given
  (hk : k ≤ K)
  (hn : n ≤ K) :
-- imply
  SchwartzMap.seminorm 𝕜 k n f ≤ (Finset.Iic (K, K)).sup (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2) f := by
-- proof
  apply Seminorm.le_def.1
  exact Finset.le_sup_of_le (Finset.mem_Iic.2 <|
    Prod.mk_le_mk.2 ⟨hk, hn⟩) le_rfl

end SchwartzSeminorms

namespace SchwartzSeminorms

/--
[monomial_le_one_add_pow_pointwise](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminormsFix.lean)
-/
@[path]
lemma monomial_le_one_add_pow_pointwise
  {K : ℕ}
  {p q : ℕ}
  {f : 𝓢(E, F)}
  {x : E}
-- given
  (hp : p ≤ K) :
-- imply
  ‖x‖ ^ p * ‖iteratedFDeriv ℝ q (⇑f) x‖ ≤ (1 + ‖x‖) ^ K * ‖iteratedFDeriv ℝ q (⇑f) x‖ := by
-- proof
  gcongr
  calc ‖x‖ ^ p ≤ (1 + ‖x‖) ^ p :=
    pow_le_pow_left₀ (norm_nonneg x) (le_add_of_nonneg_left zero_le_one) p
    _ ≤ (1 + ‖x‖) ^ K :=
      pow_le_pow_right₀ (by linarith [norm_nonneg x]) hp

end SchwartzSeminorms

namespace SchwartzSeminorms

/--
[seminorm_le_weighted_via_one_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminormsFix.lean)
-/
@[path]
lemma seminorm_le_weighted_via_one_add
  {K : ℕ}
  {p q : ℕ}
  {f : 𝓢(E, F)}
-- given
  (hp : p ≤ K)
  (hq : q ≤ K) :
-- imply
  SchwartzMap.seminorm 𝕜 p q f ≤ 2 ^ K * (Finset.Iic (K, K)).sup (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2) f := by
-- proof
  apply SchwartzMap.seminorm_le_bound 𝕜 p q f (by positivity)
  intro x
  calc ‖x‖ ^ p * ‖iteratedFDeriv ℝ q (⇑f) x‖
    ≤ (1 + ‖x‖) ^ K * ‖iteratedFDeriv ℝ q (⇑f) x‖ :=
      monomial_le_one_add_pow_pointwise hp f x
    _ ≤ 2 ^ K * (Finset.Iic (K, K)).sup (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2) f :=
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := 𝕜) (m := (K, K)) le_rfl hq f x
end SchwartzSeminorms



-- created on 2026-10-23
