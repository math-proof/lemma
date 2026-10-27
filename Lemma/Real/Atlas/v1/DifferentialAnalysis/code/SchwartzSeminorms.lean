import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.DifferentialAnalysis.code.SchwartzSeminorms
open MultiIndexBridge in TemperedDistributions
open scoped SchwartzMap


namespace TemperedDistributions

/--
[japaneseBracket_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma japaneseBracket_nonneg
  [NormedAddCommGroup E]
  {x : E} :
-- imply
  0 ≤ japaneseBracket x :=
-- proof
  Real.sqrt_nonneg _

end TemperedDistributions

namespace TemperedDistributions

/--
[japaneseBracket_le_one_add_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma japaneseBracket_le_one_add_norm
  [NormedAddCommGroup E]
  {x : E} :
-- imply
  japaneseBracket x ≤ 1 + ‖x‖ :=
-- proof
  sqrt_one_add_norm_sq_le x

end TemperedDistributions

namespace TemperedDistributions

/--
[one_add_norm_le_sqrt_two_mul_japaneseBracket](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma one_add_norm_le_sqrt_two_mul_japaneseBracket
  [NormedAddCommGroup E]
  {x : E} :
-- imply
  1 + ‖x‖ ≤ Real.sqrt 2 * japaneseBracket x :=
-- proof
  one_add_norm_le_sqrt_two_mul_sqrt x

end TemperedDistributions

namespace TemperedDistributions

/--
[japaneseBracket_pow_le_one_add_norm_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma japaneseBracket_pow_le_one_add_norm_pow
  [NormedAddCommGroup E]
  {x : E}
  {k : ℕ} :
-- imply
  japaneseBracket x ^ k ≤ (1 + ‖x‖) ^ k :=
-- proof
  pow_le_pow_left₀ (japaneseBracket_nonneg x) (japaneseBracket_le_one_add_norm x) k

end TemperedDistributions

namespace TemperedDistributions

/--
[one_add_norm_pow_le_sqrt_two_pow_mul_japaneseBracket_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma one_add_norm_pow_le_sqrt_two_pow_mul_japaneseBracket_pow
  [NormedAddCommGroup E]
  {x : E}
  {k : ℕ} :
-- imply
  (1 + ‖x‖) ^ k ≤ Real.sqrt 2 ^ k * japaneseBracket x ^ k := by
-- proof
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (one_add_norm_le_sqrt_two_mul_japaneseBracket x) k

end TemperedDistributions

namespace TemperedDistributions

/--
[weighted_norm_le_sup_seminorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
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

end TemperedDistributions

namespace TemperedDistributions

/--
[monomial_norm_le_weighted_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
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

end TemperedDistributions

namespace TemperedDistributions

/--
[weightedCkNorm_bounds_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma weightedCkNorm_bounds_nonempty
  {K n : ℕ}
  {f : 𝓢(E, F)} :
-- imply
  { c : ℝ | 0 ≤ c ∧ ∀ x, (1 + ‖x‖) ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ c }.Nonempty := by
-- proof
  obtain ⟨C₀, hC₀pos, hC₀⟩ := f.decay 0 n
  obtain ⟨C_K, hCKpos, hCK⟩ := f.decay K n
  refine ⟨2 ^ K * (C₀ + C_K), by positivity, fun x => ?_⟩
  have hC0_bound : ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ C₀ := by
    have := hC₀ x; simp only [pow_zero, one_mul] at this; exact this
  have hCK_bound : ‖x‖ ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ C_K := hCK x
  have h1 : (1 + ‖x‖) ^ K ≤ 2 ^ (K - 1) * (1 ^ K + ‖x‖ ^ K) :=
    add_pow_le zero_le_one (norm_nonneg x) K
  have h2 : (2 : ℝ) ^ (K - 1) ≤ 2 ^ K :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le K 1)
  have hxK_nonneg : (0 : ℝ) ≤ 1 + ‖x‖ ^ K := by positivity
  have h3 : (1 : ℝ) ^ K + ‖x‖ ^ K = 1 + ‖x‖ ^ K := by simp [one_pow]
  have h_add_pow : (1 + ‖x‖) ^ K ≤ 2 ^ K * (1 + ‖x‖ ^ K) := by
    calc (1 + ‖x‖) ^ K ≤ 2 ^ (K - 1) * (1 ^ K + ‖x‖ ^ K) := h1
      _ = 2 ^ (K - 1) * (1 + ‖x‖ ^ K) := by rw [h3]
      _ ≤ 2 ^ K * (1 + ‖x‖ ^ K) := by
        exact mul_le_mul_of_nonneg_right h2 hxK_nonneg
  calc (1 + ‖x‖) ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖
    ≤ 2 ^ K * (1 + ‖x‖ ^ K) * ‖iteratedFDeriv ℝ n (⇑f) x‖ :=
      mul_le_mul_of_nonneg_right h_add_pow (norm_nonneg _)
    _ = 2 ^ K * (‖iteratedFDeriv ℝ n (⇑f) x‖ + ‖x‖ ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖) := by
      ring
    _ ≤ 2 ^ K * (C₀ + C_K) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith [hC0_bound, hCK_bound]

end TemperedDistributions

namespace TemperedDistributions

/--
[weightedCkNorm_bounds_bddBelow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma weightedCkNorm_bounds_bddBelow
  {K n : ℕ}
  {f : 𝓢(E, F)} :
-- imply
  BddBelow { c : ℝ | 0 ≤ c ∧ ∀ x, (1 + ‖x‖) ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ c } :=
-- proof
  ⟨0, fun _ hc => hc.1⟩

end TemperedDistributions

namespace TemperedDistributions

/--
[weightedCkNorm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma weightedCkNorm_nonneg
  {K n : ℕ}
  {f : 𝓢(E, F)} :
-- imply
  0 ≤ weightedCkNorm K n f :=
-- proof
  le_csInf (weightedCkNorm_bounds_nonempty K n f) fun _ hc => hc.1

end TemperedDistributions

namespace TemperedDistributions

/--
[le_weightedCkNorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma le_weightedCkNorm
  {K n : ℕ}
  {f : 𝓢(E, F)}
  {x : E} :
-- imply
  (1 + ‖x‖) ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ weightedCkNorm K n f :=
-- proof
  le_csInf (weightedCkNorm_bounds_nonempty K n f) fun _ hc => hc.2 x

end TemperedDistributions

namespace TemperedDistributions

/--
[weightedCkNorm_le_sup_seminorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma weightedCkNorm_le_sup_seminorm
  {K : ℕ}
  {n : ℕ}
  {f : 𝓢(E, F)}
-- given
  (hn : n ≤ K) :
-- imply
  weightedCkNorm K n f ≤ 2 ^ K * (Finset.Iic (K, K)).sup (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2) f := by
-- proof
  apply csInf_le (weightedCkNorm_bounds_bddBelow K n f)
  exact ⟨by positivity, fun x =>
    SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := 𝕜) (m := (K, K)) le_rfl hn f x⟩

end TemperedDistributions

namespace TemperedDistributions

/--
[seminorm_le_weightedCkNorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma seminorm_le_weightedCkNorm
  {K : ℕ}
  {k n : ℕ}
  {f : 𝓢(E, F)}
-- given
  (hk : k ≤ K) :
-- imply
  SchwartzMap.seminorm 𝕜 k n f ≤ weightedCkNorm K n f := by
-- proof
  apply SchwartzMap.seminorm_le_bound 𝕜 k n f (weightedCkNorm_nonneg K n f)
  intro x
  have h1 : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k :=
    pow_le_pow_left₀ (norm_nonneg x) (le_add_of_nonneg_left zero_le_one) k
  have h2 : (1 + ‖x‖) ^ k ≤ (1 + ‖x‖) ^ K :=
    pow_le_pow_right₀ (by linarith [norm_nonneg x] : 1 ≤ 1 + ‖x‖) hk
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑f) x‖
    ≤ (1 + ‖x‖) ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact le_trans h1 h2
    _ ≤ weightedCkNorm K n f := le_weightedCkNorm K n f x

end TemperedDistributions

namespace TemperedDistributions

/--
[weightedCkNorm_le_weightedCkNormSup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma weightedCkNorm_le_weightedCkNormSup
  {K : ℕ}
  {n : ℕ}
  {f : 𝓢(E, F)}
-- given
  (hn : n ≤ K) :
-- imply
  weightedCkNorm (E := E) (F := F) K n f ≤ weightedCkNormSup (E := E) (F := F) K f := by
-- proof
  unfold weightedCkNormSup
  exact Finset.le_sup' (fun n => weightedCkNorm (E := E) (F := F) K n f)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))

end TemperedDistributions

namespace TemperedDistributions

/--
[seminorm_le_weightedCkNormSup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma seminorm_le_weightedCkNormSup
  {K : ℕ}
  {k n : ℕ}
  {f : 𝓢(E, F)}
-- given
  (hk : k ≤ K)
  (hn : n ≤ K) :
-- imply
  SchwartzMap.seminorm 𝕜 k n f ≤ weightedCkNormSup (E := E) (F := F) K f :=
-- proof
  le_trans (seminorm_le_weightedCkNorm hk f) (weightedCkNorm_le_weightedCkNormSup K hn f)

end TemperedDistributions

namespace TemperedDistributions

/--
[weightedCkNormSup_le_sup_seminorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma weightedCkNormSup_le_sup_seminorm
  {K : ℕ}
  {f : 𝓢(E, F)} :
-- imply
  weightedCkNormSup (E := E) (F := F) K f ≤ 2 ^ K * (Finset.Iic (K, K)).sup (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2) f := by
-- proof
  unfold weightedCkNormSup
  simp only [Finset.sup'_le_iff, Finset.mem_range]
  intro n hn
  exact weightedCkNorm_le_sup_seminorm (Nat.lt_succ_iff.mp hn) f

end TemperedDistributions

namespace TemperedDistributions

/--
[monomialDerivNormSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma monomialDerivNormSum_nonneg
  {K : ℕ}
  {f : 𝓢(E, F)} :
-- imply
  0 ≤ monomialDerivNormSum (𝕜 := 𝕜) (E := E) (F := F) K f :=
-- proof
  Finset.sum_nonneg fun m _ => apply_nonneg (SchwartzMap.seminorm 𝕜 m.1 m.2) f

end TemperedDistributions

namespace TemperedDistributions

/--
[sup_seminorm_le_monomialDerivNormSum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma sup_seminorm_le_monomialDerivNormSum
  {K : ℕ}
  {f : 𝓢(E, F)} :
-- imply
  (Finset.Iic (K, K)).sup (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2) f ≤ monomialDerivNormSum (𝕜 := 𝕜) (E := E) (F := F) K f := by
-- proof
  unfold monomialDerivNormSum
  apply Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun m _ =>
    apply_nonneg (SchwartzMap.seminorm 𝕜 m.1 m.2) f)
  intro i hi
  exact Finset.single_le_sum (fun m _ => apply_nonneg (SchwartzMap.seminorm 𝕜 m.1 m.2) f) hi

end TemperedDistributions

namespace TemperedDistributions

/--
[card_Iic_pair](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma card_Iic_pair
  {K : ℕ} :
-- imply
  (Finset.Iic (K, K)).card = (K + 1) ^ 2 := by
-- proof
  rw [Finset.card_Iic_prod]
  simp [Nat.card_Iic, sq]

end TemperedDistributions

namespace TemperedDistributions

/--
[weightedCkNormSup_le_two_pow_mul_monomialDerivNormSum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma weightedCkNormSup_le_two_pow_mul_monomialDerivNormSum
  {K : ℕ}
  {f : 𝓢(E, F)} :
-- imply
  weightedCkNormSup (E := E) (F := F) K f ≤ 2 ^ K * monomialDerivNormSum (𝕜 := 𝕜) (E := E) (F := F) K f := by
-- proof
  calc weightedCkNormSup (E := E) (F := F) K f
    ≤ 2 ^ K * (Finset.Iic (K, K)).sup (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2) f :=
      weightedCkNormSup_le_sup_seminorm K f
    _ ≤ 2 ^ K * monomialDerivNormSum (𝕜 := 𝕜) (E := E) (F := F) K f := by
      apply mul_le_mul_of_nonneg_left (sup_seminorm_le_monomialDerivNormSum K f)
      positivity

end TemperedDistributions

namespace TemperedDistributions

/--
[monomialDerivNormSum_le_sq_mul_weightedCkNormSup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma monomialDerivNormSum_le_sq_mul_weightedCkNormSup
  {K : ℕ}
  {f : 𝓢(E, F)} :
-- imply
  monomialDerivNormSum (𝕜 := 𝕜) (E := E) (F := F) K f ≤ ((K + 1) ^ 2 : ℕ) * weightedCkNormSup (E := E) (F := F) K f := by
-- proof
  unfold monomialDerivNormSum
  have hbound : ∀ m ∈ Finset.Iic (K, K),
    (SchwartzMap.seminorm 𝕜 m.1 m.2) f ≤ weightedCkNormSup (E := E) (F := F) K f := by
    intro m hm
    exact seminorm_le_weightedCkNormSup (Finset.mem_Iic.mp hm).1 (Finset.mem_Iic.mp hm).2 f
  have h1 := Finset.sum_le_card_nsmul _ _ _ hbound
  rw [card_Iic_pair] at h1
  rwa [nsmul_eq_mul] at h1
end TemperedDistributions
namespace MultiIndexBridge
open scoped SchwartzMap
noncomputable section


namespace MultiIndexBridge

/--
[multiIndexOrder_tupleToMultiIndex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma multiIndexOrder_tupleToMultiIndex
  {m : ℕ}
  {n : ℕ}
  {σ : Fin n → Fin m} :
-- imply
  multiIndexOrder (tupleToMultiIndex σ) = n := by
-- proof
  have h := Finset.card_eq_sum_card_fiberwise (f := σ)
    (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_fin] at h
  simp only [multiIndexOrder, tupleToMultiIndex]
  exact h.symm

end MultiIndexBridge

namespace MultiIndexBridge

/--
[multiIndexDirections_eq_single](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma multiIndexDirections_eq_single
  {m : ℕ}
  {β : Fin m → ℕ}
  {k : Fin (multiIndexOrder β)} :
-- imply
  ∃ i : Fin m, multiIndexDirections β k = EuclideanSpace.single i 1 :=
-- proof
  ⟨_, rfl⟩

end MultiIndexBridge

namespace MultiIndexBridge

/--
[norm_multiIndexDirections_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma norm_multiIndexDirections_le
  {m : ℕ}
  {β : Fin m → ℕ}
  {k : Fin (multiIndexOrder β)} :
-- imply
  ‖multiIndexDirections β k‖ ≤ 1 := by
-- proof
  obtain ⟨i, hi⟩ := multiIndexDirections_eq_single β k
  rw [hi, PiLp.norm_single]
  simp

end MultiIndexBridge

namespace MultiIndexBridge

/--
[abs_realMonomial_le_norm_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma abs_realMonomial_le_norm_pow
  {m : ℕ}
  {α : Fin m → ℕ}
  {x : EuclideanSpace ℝ (Fin m)} :
-- imply
  |realMonomial α x| ≤ ‖x‖ ^ multiIndexOrder α := by
-- proof
  simp only [realMonomial, multiIndexOrder]
  rw [← Finset.prod_pow_eq_pow_sum, Finset.abs_prod]
  apply Finset.prod_le_prod
  · intro i _
    positivity
  · intro i _
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _)
      (by rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le x i) _

end MultiIndexBridge

namespace MultiIndexBridge

/--
[norm_multiIndexPartialDeriv_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma norm_multiIndexPartialDeriv_le
  {m : ℕ}
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  {β : Fin m → ℕ}
  {f : EuclideanSpace ℝ (Fin m) → F}
  {x : EuclideanSpace ℝ (Fin m)} :
-- imply
  ‖multiIndexPartialDeriv β f x‖ ≤ ‖iteratedFDeriv ℝ (multiIndexOrder β) f x‖ := by
-- proof
  simp only [multiIndexPartialDeriv]
  calc ‖(iteratedFDeriv ℝ (multiIndexOrder β) f x) (multiIndexDirections β)‖
    ≤ ‖iteratedFDeriv ℝ (multiIndexOrder β) f x‖ * ∏ k, ‖multiIndexDirections β k‖ :=
      (iteratedFDeriv ℝ (multiIndexOrder β) f x).le_opNorm _
    _ ≤ ‖iteratedFDeriv ℝ (multiIndexOrder β) f x‖ * 1 := by
      gcongr
      apply Finset.prod_le_one (fun k _ => norm_nonneg _)
      intro k _
      exact norm_multiIndexDirections_le β k
    _ = ‖iteratedFDeriv ℝ (multiIndexOrder β) f x‖ := mul_one _
end
end MultiIndexBridge
open MultiIndexBridge in
open scoped SchwartzMap in
/-- The iterated Fréchet derivative norm of a Schwartz function is bounded by the sum over tuples of the corresponding mixed partial derivative norms. -/
namespace MultiIndexBridge
open scoped SchwartzMap
noncomputable section
variable {𝕜 : Type*} [NormedField 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

end MultiIndexBridge

namespace MultiIndexBridge

/--
[monomial_iteratedFDeriv_le_seminorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma monomial_iteratedFDeriv_le_seminorm
  [NormedField 𝕜]
  {α β : Fin m → ℕ}
  {f : 𝓢(EuclideanSpace ℝ (Fin m), F)}
  {x : EuclideanSpace ℝ (Fin m)} :
-- imply
  |realMonomial α x| * ‖iteratedFDeriv ℝ (multiIndexOrder β) (⇑f) x‖ ≤ SchwartzMap.seminorm 𝕜 (multiIndexOrder α) (multiIndexOrder β) f :=
-- proof
  calc |realMonomial α x| * ‖iteratedFDeriv ℝ (multiIndexOrder β) (⇑f) x‖
    ≤ ‖x‖ ^ multiIndexOrder α * ‖iteratedFDeriv ℝ (multiIndexOrder β) (⇑f) x‖ :=
      mul_le_mul_of_nonneg_right (abs_realMonomial_le_norm_pow α x) (norm_nonneg _)
    _ ≤ SchwartzMap.seminorm 𝕜 (multiIndexOrder α) (multiIndexOrder β) f :=
      SchwartzMap.le_seminorm 𝕜 (multiIndexOrder α) (multiIndexOrder β) f x

end MultiIndexBridge

namespace MultiIndexBridge

/--
[norm_le_sum_abs](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma norm_le_sum_abs
  [NormedField 𝕜]
  {x : EuclideanSpace ℝ (Fin m)} :
-- imply
  ‖x‖ ≤ ∑ i : Fin m, |x i| := by
-- proof
  refine le_of_sq_le_sq ?_ (Finset.sum_nonneg fun i _ => abs_nonneg _)
  rw [EuclideanSpace.real_norm_sq_eq]
  calc ∑ i : Fin m, (x i) ^ 2
    = ∑ i : Fin m, |x i| ^ 2 := by
      congr 1; ext i; rw [sq_abs]
    _ ≤ (∑ i : Fin m, |x i|) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => abs_nonneg (x i))

end MultiIndexBridge

namespace MultiIndexBridge

/--
[norm_pow_le_sum_coord_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma norm_pow_le_sum_coord_pow
  [NormedField 𝕜]
  {x : EuclideanSpace ℝ (Fin m)}
  {k : ℕ} :
-- imply
  ‖x‖ ^ (k + 1) ≤ (m : ℝ) ^ k * ∑ i : Fin m, |x i| ^ (k + 1) := by
-- proof
  calc ‖x‖ ^ (k + 1)
    ≤ (∑ i : Fin m, |x i|) ^ (k + 1) :=
      pow_le_pow_left₀ (norm_nonneg x) (norm_le_sum_abs x) (k + 1)
    _ ≤ (↑(Finset.univ : Finset (Fin m)).card : ℝ) ^ k *
      ∑ i ∈ Finset.univ, |x i| ^ (k + 1) := by
      exact pow_sum_le_card_mul_sum_pow
        (fun i _ => abs_nonneg (x i)) k
    _ = (m : ℝ) ^ k * ∑ i : Fin m, |x i| ^ (k + 1) := by
      rw [Finset.card_fin]

end MultiIndexBridge

namespace MultiIndexBridge

/--
[multiIndexOrder_coordMultiIndex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma multiIndexOrder_coordMultiIndex
  [NormedField 𝕜]
  {k : ℕ}
  {i : Fin m} :
-- imply
  multiIndexOrder (coordMultiIndex k i) = k := by
-- proof
  simp only [multiIndexOrder, coordMultiIndex]
  rw [Finset.sum_ite_eq']
  simp [Finset.mem_univ]

end MultiIndexBridge

namespace MultiIndexBridge

/--
[abs_coord_pow_eq_abs_realMonomial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma abs_coord_pow_eq_abs_realMonomial
  [NormedField 𝕜]
  {x : EuclideanSpace ℝ (Fin m)}
  {i : Fin m}
  {k : ℕ} :
-- imply
  |x i| ^ k = |realMonomial (coordMultiIndex k i) x| := by
-- proof
  simp only [realMonomial, coordMultiIndex]
  rw [Finset.abs_prod]
  have : ∀ j : Fin m, |x j ^ (if j = i then k else 0)| =
    if j = i then |x j| ^ k else 1 := by
    intro j
    split_ifs with h
    · rw [abs_pow]
    · simp
  simp_rw [this]
  rw [Finset.prod_ite_eq']
  simp [Finset.mem_univ]

end MultiIndexBridge

namespace MultiIndexBridge

/--
[mem_boundedMultiIndices_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma mem_boundedMultiIndices_iff
  [NormedField 𝕜]
  {α : Fin m → ℕ}
  {K : ℕ} :
-- imply
  α ∈ boundedMultiIndices m K ↔ ∀ i, α i ≤ K := by
-- proof
  simp [boundedMultiIndices, Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff]

end MultiIndexBridge

namespace MultiIndexBridge

/--
[mem_boundedMultiIndices_of_multiIndexOrder_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma mem_boundedMultiIndices_of_multiIndexOrder_le
  [NormedField 𝕜]
  {α : Fin m → ℕ}
  {K : ℕ}
-- given
  (hα : multiIndexOrder α ≤ K) :
-- imply
  α ∈ boundedMultiIndices m K := by
-- proof
  rw [mem_boundedMultiIndices_iff]
  intro i
  calc α i ≤ ∑ j, α j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    _ = multiIndexOrder α := rfl
    _ ≤ K := hα

end MultiIndexBridge

namespace MultiIndexBridge

/--
[card_boundedMultiIndices](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma card_boundedMultiIndices
  [NormedField 𝕜]
  {m K : ℕ} :
-- imply
  (boundedMultiIndices m K).card = (K + 1) ^ m := by
-- proof
  simp [boundedMultiIndices, Fintype.card_piFinset, Finset.card_range]

end MultiIndexBridge

namespace MultiIndexBridge

/--
[mem_totalOrderBoundedMultiIndices_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma mem_totalOrderBoundedMultiIndices_iff
  [NormedField 𝕜]
  {α : Fin m → ℕ}
  {K : ℕ} :
-- imply
  α ∈ totalOrderBoundedMultiIndices m K ↔ multiIndexOrder α ≤ K := by
-- proof
  simp only [totalOrderBoundedMultiIndices, Finset.mem_filter]
  constructor
  · exact fun ⟨_, h⟩ => h
  · exact fun h => ⟨mem_boundedMultiIndices_of_multiIndexOrder_le h, h⟩

end MultiIndexBridge

namespace MultiIndexBridge

/--
[coordMultiIndex_mem_totalOrderBoundedMultiIndices](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma coordMultiIndex_mem_totalOrderBoundedMultiIndices
  [NormedField 𝕜]
  {k : ℕ}
  {i : Fin m}
  {K : ℕ}
-- given
  (hk : k ≤ K) :
-- imply
  coordMultiIndex k i ∈ totalOrderBoundedMultiIndices m K := by
-- proof
  rw [mem_totalOrderBoundedMultiIndices_iff]
  rwa [multiIndexOrder_coordMultiIndex]

end MultiIndexBridge

namespace MultiIndexBridge

/--
[tupleToMultiIndex_mem_totalOrderBoundedMultiIndices](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma tupleToMultiIndex_mem_totalOrderBoundedMultiIndices
  [NormedField 𝕜]
  {n : ℕ}
  {σ : Fin n → Fin m}
  {K : ℕ}
-- given
  (hn : n ≤ K) :
-- imply
  tupleToMultiIndex σ ∈ totalOrderBoundedMultiIndices m K := by
-- proof
  rwa [mem_totalOrderBoundedMultiIndices_iff, multiIndexOrder_tupleToMultiIndex]

end MultiIndexBridge

namespace MultiIndexBridge

/--
[monomialDerivSupNorm_bounds_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma monomialDerivSupNorm_bounds_nonempty
  [NormedField 𝕜]
  {α β : Fin m → ℕ}
  {f : 𝓢(EuclideanSpace ℝ (Fin m), F)} :
-- imply
  ∃ c, c ∈ { c | 0 ≤ c ∧ ∀ x, |realMonomial α x| * ‖multiIndexPartialDeriv β (⇑f) x‖ ≤ c } := by
-- proof
  obtain ⟨M, hMp, hMb⟩ := f.decay (multiIndexOrder α) (multiIndexOrder β)
  exact ⟨M, le_of_lt hMp, fun x =>
    calc |realMonomial α x| * ‖multiIndexPartialDeriv β (⇑f) x‖
      ≤ |realMonomial α x| * ‖iteratedFDeriv ℝ (multiIndexOrder β) (⇑f) x‖ :=
        mul_le_mul_of_nonneg_left (norm_multiIndexPartialDeriv_le β (⇑f) x) (abs_nonneg _)
      _ ≤ ‖x‖ ^ multiIndexOrder α * ‖iteratedFDeriv ℝ (multiIndexOrder β) (⇑f) x‖ :=
        mul_le_mul_of_nonneg_right (abs_realMonomial_le_norm_pow α x) (norm_nonneg _)
      _ ≤ M := hMb x⟩

end MultiIndexBridge

namespace MultiIndexBridge

/--
[monomialDerivSupNorm_bounds_bddBelow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma monomialDerivSupNorm_bounds_bddBelow
  [NormedField 𝕜]
  {α β : Fin m → ℕ}
  {f : 𝓢(EuclideanSpace ℝ (Fin m), F)} :
-- imply
  BddBelow { c | 0 ≤ c ∧ ∀ x, |realMonomial α x| * ‖multiIndexPartialDeriv β (⇑f) x‖ ≤ c } :=
-- proof
  ⟨0, fun _ ⟨hc, _⟩ => hc⟩

end MultiIndexBridge

namespace MultiIndexBridge

/--
[monomialDerivSupNorm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma monomialDerivSupNorm_nonneg
  [NormedField 𝕜]
  {α β : Fin m → ℕ}
  {f : 𝓢(EuclideanSpace ℝ (Fin m), F)} :
-- imply
  0 ≤ monomialDerivSupNorm α β f :=
-- proof
  le_csInf (monomialDerivSupNorm_bounds_nonempty α β f) fun _ ⟨hc, _⟩ => hc

end MultiIndexBridge

namespace MultiIndexBridge

/--
[le_monomialDerivSupNorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma le_monomialDerivSupNorm
  [NormedField 𝕜]
  {α β : Fin m → ℕ}
  {f : 𝓢(EuclideanSpace ℝ (Fin m), F)}
  {x : EuclideanSpace ℝ (Fin m)} :
-- imply
  |realMonomial α x| * ‖multiIndexPartialDeriv β (⇑f) x‖ ≤ monomialDerivSupNorm α β f :=
-- proof
  le_csInf (monomialDerivSupNorm_bounds_nonempty α β f) fun _ ⟨_, hb⟩ => hb x

end MultiIndexBridge

namespace MultiIndexBridge

/--
[monomialDerivSupNorm_le_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma monomialDerivSupNorm_le_bound
  [NormedField 𝕜]
  {α β : Fin m → ℕ}
  {f : 𝓢(EuclideanSpace ℝ (Fin m), F)}
  {M : ℝ}
-- given
  (hMp : 0 ≤ M)
  (hM : ∀ x, |realMonomial α x| * ‖multiIndexPartialDeriv β (⇑f) x‖ ≤ M) :
-- imply
  monomialDerivSupNorm α β f ≤ M :=
-- proof
  csInf_le (monomialDerivSupNorm_bounds_bddBelow α β f) ⟨hMp, hM⟩

end MultiIndexBridge

namespace MultiIndexBridge

/--
[monomialDerivSupNorm_le_seminorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma monomialDerivSupNorm_le_seminorm
  [NormedField 𝕜]
  {α β : Fin m → ℕ}
  {f : 𝓢(EuclideanSpace ℝ (Fin m), F)} :
-- imply
  monomialDerivSupNorm α β f ≤ SchwartzMap.seminorm 𝕜 (multiIndexOrder α) (multiIndexOrder β) f := by
-- proof
  apply monomialDerivSupNorm_le_bound α β f
    (apply_nonneg (SchwartzMap.seminorm 𝕜 (multiIndexOrder α) (multiIndexOrder β)) f)
  intro x
  calc |realMonomial α x| * ‖multiIndexPartialDeriv β (⇑f) x‖
    ≤ |realMonomial α x| * ‖iteratedFDeriv ℝ (multiIndexOrder β) (⇑f) x‖ :=
      mul_le_mul_of_nonneg_left (norm_multiIndexPartialDeriv_le β (⇑f) x) (abs_nonneg _)
    _ ≤ SchwartzMap.seminorm 𝕜 (multiIndexOrder α) (multiIndexOrder β) f :=
      monomial_iteratedFDeriv_le_seminorm α β f x

end MultiIndexBridge

namespace MultiIndexBridge

/--
[bookMultiIndexNorm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma bookMultiIndexNorm_nonneg
  [NormedField 𝕜]
  {K : ℕ}
  {f : 𝓢(EuclideanSpace ℝ (Fin m), F)} :
-- imply
  0 ≤ bookMultiIndexNorm K f :=
-- proof
  Finset.sum_nonneg fun α _ =>
    Finset.sum_nonneg fun β _ =>
      monomialDerivSupNorm_nonneg α β f

end MultiIndexBridge

namespace MultiIndexBridge

/--
[bookMultiIndexNorm_le_monomialDerivNormSum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma bookMultiIndexNorm_le_monomialDerivNormSum
  [NormedField 𝕜]
  {K : ℕ}
  {f : 𝓢(EuclideanSpace ℝ (Fin m), F)} :
-- imply
  bookMultiIndexNorm K f ≤ (((K + 1) ^ m : ℕ) ^ 2 : ℕ) * TemperedDistributions.monomialDerivNormSum (𝕜 := 𝕜) K f := by
-- proof
  unfold bookMultiIndexNorm
  have hterm : ∀ α ∈ totalOrderBoundedMultiIndices m K,
    ∀ β ∈ totalOrderBoundedMultiIndices m K,
    monomialDerivSupNorm α β f ≤
      TemperedDistributions.monomialDerivNormSum (𝕜 := 𝕜) K f := by
    intro α hα β hβ
    rw [mem_totalOrderBoundedMultiIndices_iff] at hα hβ
    calc monomialDerivSupNorm α β f
      ≤ SchwartzMap.seminorm 𝕜 (multiIndexOrder α) (multiIndexOrder β) f :=
        monomialDerivSupNorm_le_seminorm α β f
      _ ≤ TemperedDistributions.monomialDerivNormSum (𝕜 := 𝕜) K f :=
        Finset.single_le_sum
          (fun p _ => apply_nonneg (SchwartzMap.seminorm 𝕜 p.1 p.2) f)
          (Finset.mem_Iic.2 (Prod.mk_le_mk.2 ⟨hα, hβ⟩))
  have hcard_le : (totalOrderBoundedMultiIndices m K).card ≤ (K + 1) ^ m := by
    calc (totalOrderBoundedMultiIndices m K).card
      ≤ (boundedMultiIndices m K).card := Finset.card_filter_le _ _
      _ = (K + 1) ^ m := card_boundedMultiIndices m K
  have hinner : ∀ α ∈ totalOrderBoundedMultiIndices m K,
    ∑ β ∈ totalOrderBoundedMultiIndices m K, monomialDerivSupNorm α β f ≤
      ((K + 1) ^ m : ℕ) * TemperedDistributions.monomialDerivNormSum (𝕜 := 𝕜) K f := by
    intro α hα
    have h := Finset.sum_le_card_nsmul _ _ _ (fun β hβ => hterm α hα β hβ)
    rw [nsmul_eq_mul] at h
    calc ∑ β ∈ totalOrderBoundedMultiIndices m K, monomialDerivSupNorm α β f
      ≤ (totalOrderBoundedMultiIndices m K).card *
        TemperedDistributions.monomialDerivNormSum (𝕜 := 𝕜) K f := h
      _ ≤ ((K + 1) ^ m : ℕ) *
        TemperedDistributions.monomialDerivNormSum (𝕜 := 𝕜) K f := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hcard_le
        · exact TemperedDistributions.monomialDerivNormSum_nonneg K f
  have houter := Finset.sum_le_card_nsmul _ _ _ hinner
  rw [nsmul_eq_mul] at houter
  calc ∑ α ∈ totalOrderBoundedMultiIndices m K,
    ∑ β ∈ totalOrderBoundedMultiIndices m K, monomialDerivSupNorm α β f
    ≤ (totalOrderBoundedMultiIndices m K).card *
      (((K + 1) ^ m : ℕ) *
        TemperedDistributions.monomialDerivNormSum (𝕜 := 𝕜) K f) := houter
    _ ≤ ((K + 1) ^ m : ℕ) *
      (((K + 1) ^ m : ℕ) *
        TemperedDistributions.monomialDerivNormSum (𝕜 := 𝕜) K f) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hcard_le
      · apply mul_nonneg
        · positivity
        · exact TemperedDistributions.monomialDerivNormSum_nonneg K f
    _ = (((K + 1) ^ m : ℕ) ^ 2 : ℕ) *
      TemperedDistributions.monomialDerivNormSum (𝕜 := 𝕜) K f := by
      push_cast; ring

end MultiIndexBridge

namespace MultiIndexBridge

/--
[euclidean_sum_single_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma euclidean_sum_single_decomp
  [NormedField 𝕜]
  {v : EuclideanSpace ℝ (Fin m)} :
-- imply
  v = ∑ i : Fin m, (v i) • EuclideanSpace.single i (1 : ℝ) := by
-- proof
  have h := (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr v
  rw [show (EuclideanSpace.basisFun (Fin m) ℝ).repr v = v from by
    simp [EuclideanSpace.basisFun]] at h
  simp only [show ∀ i, (EuclideanSpace.basisFun (Fin m) ℝ) i = EuclideanSpace.single i 1 from by
    intro i; simp [EuclideanSpace.basisFun]; rfl] at h
  exact h.symm

end MultiIndexBridge

namespace MultiIndexBridge

/--
[multilinear_basis_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma multilinear_basis_expansion
  [NormedField 𝕜]
  {n : ℕ}
  {v : Fin n → EuclideanSpace ℝ (Fin m)}
-- given
  (M : ContinuousMultilinearMap ℝ (fun _ : Fin n => EuclideanSpace ℝ (Fin m)) F) :
-- imply
  M v = ∑ σ : Fin n → Fin m, (∏ k, (v k) (σ k)) • M (fun k => EuclideanSpace.single (σ k) 1) := by
-- proof
  conv_lhs =>
    rw [show v = fun k => ∑ i : Fin m, (v k i) • EuclideanSpace.single i 1 from
      funext (fun k => euclidean_sum_single_decomp (v k))]
  rw [M.map_sum_finset (fun k i => (v k i) • EuclideanSpace.single i 1) (fun _ => Finset.univ)]
  simp only [Fintype.piFinset_univ]
  congr 1; ext σ
  exact M.map_smul_univ (fun k => (v k) (σ k)) (fun k => EuclideanSpace.single (σ k) 1)
end
namespace TemperedDistributions
open MultiIndexBridge
open scoped SchwartzMap
end TemperedDistributions
open MultiIndexBridge in
open scoped SchwartzMap in
namespace TemperedDistributions
open scoped SchwartzMap
open MultiIndexBridge
noncomputable section


namespace TemperedDistributions

/--
[japaneseBracketCkNorm_bounds_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma japaneseBracketCkNorm_bounds_nonempty
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {K n : ℕ}
  {f : 𝓢(E, F)} :
-- imply
  { c : ℝ | 0 ≤ c ∧ ∀ x, japaneseBracket x ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ c }.Nonempty := by
-- proof
  have h := weightedCkNorm_bounds_nonempty (E := E) K n f
  obtain ⟨c, hc0, hcb⟩ := h
  refine ⟨c, hc0, fun x => ?_⟩
  calc japaneseBracket x ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖
    ≤ (1 + ‖x‖) ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖ :=
      mul_le_mul_of_nonneg_right (japaneseBracket_pow_le_one_add_norm_pow x K) (norm_nonneg _)
    _ ≤ c := hcb x

end TemperedDistributions

namespace TemperedDistributions

/--
[japaneseBracketCkNorm_bounds_bddBelow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma japaneseBracketCkNorm_bounds_bddBelow
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {K n : ℕ}
  {f : 𝓢(E, F)} :
-- imply
  BddBelow { c : ℝ | 0 ≤ c ∧ ∀ x, japaneseBracket x ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ c } :=
-- proof
  ⟨0, fun _ hc => hc.1⟩

end TemperedDistributions

namespace TemperedDistributions

/--
[japaneseBracketCkNorm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma japaneseBracketCkNorm_nonneg
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {K n : ℕ}
  {f : 𝓢(E, F)} :
-- imply
  0 ≤ japaneseBracketCkNorm (F := F) K n f :=
-- proof
  le_csInf (japaneseBracketCkNorm_bounds_nonempty K n f) fun _ hc => hc.1

end TemperedDistributions

namespace TemperedDistributions

/--
[le_japaneseBracketCkNorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma le_japaneseBracketCkNorm
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {K n : ℕ}
  {f : 𝓢(E, F)}
  {x : E} :
-- imply
  japaneseBracket x ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ japaneseBracketCkNorm K n f :=
-- proof
  le_csInf (japaneseBracketCkNorm_bounds_nonempty K n f) fun _ ⟨_, hb⟩ => hb x

end TemperedDistributions

namespace TemperedDistributions

/--
[japaneseBracketCkNorm_le_weightedCkNorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma japaneseBracketCkNorm_le_weightedCkNorm
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {K n : ℕ}
  {f : 𝓢(E, F)} :
-- imply
  japaneseBracketCkNorm (F := F) K n f ≤ weightedCkNorm K n f := by
-- proof
  apply csInf_le (japaneseBracketCkNorm_bounds_bddBelow K n f)
  refine ⟨weightedCkNorm_nonneg K n f, fun x => ?_⟩
  calc japaneseBracket x ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖
    ≤ (1 + ‖x‖) ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖ :=
      mul_le_mul_of_nonneg_right (japaneseBracket_pow_le_one_add_norm_pow x K) (norm_nonneg _)
    _ ≤ weightedCkNorm K n f := le_weightedCkNorm K n f x

end TemperedDistributions

namespace TemperedDistributions

/--
[weightedCkNorm_le_sqrt_two_pow_mul_japaneseBracketCkNorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma weightedCkNorm_le_sqrt_two_pow_mul_japaneseBracketCkNorm
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {K n : ℕ}
  {f : 𝓢(E, F)} :
-- imply
  weightedCkNorm (E := E) K n f ≤ Real.sqrt 2 ^ K * japaneseBracketCkNorm (F := F) K n f := by
-- proof
  have hjb_nn := japaneseBracketCkNorm_nonneg (E := E) K n f
  apply csInf_le (weightedCkNorm_bounds_bddBelow K n f)
  refine ⟨mul_nonneg (pow_nonneg (Real.sqrt_nonneg 2) K) hjb_nn, fun x => ?_⟩
  have hle := le_japaneseBracketCkNorm (E := E) K n f x
  calc (1 + ‖x‖) ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖
    ≤ (Real.sqrt 2 ^ K * japaneseBracket x ^ K) * ‖iteratedFDeriv ℝ n (⇑f) x‖ :=
      mul_le_mul_of_nonneg_right
        (one_add_norm_pow_le_sqrt_two_pow_mul_japaneseBracket_pow x K) (norm_nonneg _)
    _ = Real.sqrt 2 ^ K * (japaneseBracket x ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖) := by ring
    _ ≤ Real.sqrt 2 ^ K * japaneseBracketCkNorm K n f :=
      mul_le_mul_of_nonneg_left hle (pow_nonneg (Real.sqrt_nonneg 2) K)

end TemperedDistributions

namespace TemperedDistributions

/--
[japaneseBracketCkNormSup_le_weightedCkNormSup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma japaneseBracketCkNormSup_le_weightedCkNormSup
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {K : ℕ}
  {f : 𝓢(E, F)} :
-- imply
  japaneseBracketCkNormSup (E := E) (F := F) K f ≤ weightedCkNormSup (E := E) (F := F) K f := by
-- proof
  apply Finset.sup'_le _ _ (fun n hn => ?_)
  calc japaneseBracketCkNorm K n f
    ≤ weightedCkNorm K n f := japaneseBracketCkNorm_le_weightedCkNorm K n f
    _ ≤ weightedCkNormSup K f :=
      Finset.le_sup' (fun n => weightedCkNorm (E := E) (F := F) K n f) hn

end TemperedDistributions

namespace TemperedDistributions

/--
[weightedCkNormSup_le_sqrt_two_pow_mul_japaneseBracketCkNormSup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean)
-/
@[path]
lemma weightedCkNormSup_le_sqrt_two_pow_mul_japaneseBracketCkNormSup
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {K : ℕ}
  {f : 𝓢(E, F)} :
-- imply
  weightedCkNormSup (E := E) (F := F) K f ≤ Real.sqrt 2 ^ K * japaneseBracketCkNormSup (E := E) (F := F) K f := by
-- proof
  apply Finset.sup'_le _ _ (fun n hn => ?_)
  calc weightedCkNorm K n f
    ≤ Real.sqrt 2 ^ K * japaneseBracketCkNorm (F := F) K n f :=
      weightedCkNorm_le_sqrt_two_pow_mul_japaneseBracketCkNorm K n f
    _ ≤ Real.sqrt 2 ^ K * japaneseBracketCkNormSup K f :=
      mul_le_mul_of_nonneg_left
        (Finset.le_sup' (fun n => japaneseBracketCkNorm (E := E) (F := F) K n f) hn)
        (pow_nonneg (Real.sqrt_nonneg 2) K)
end
end TemperedDistributions
open MultiIndexBridge TemperedDistributions in
open scoped SchwartzMap in
/-- Corollary 7.2 (Melrose): equivalence of the Japanese-bracket weighted `C^K` norm and the book multi-index norm up to constants `C₁, C₂ > 0`. -/



-- created on 2026-10-23
