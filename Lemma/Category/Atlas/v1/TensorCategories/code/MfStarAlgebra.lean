import Mathlib
import sympy.Basic
import Def.v1.Atlas.TensorCategories.code.MfStarAlgebra.Part3
open Finset Complex MultifusionRingDef MfGrRingOfC


namespace MultifusionRingDef

/--
[star_eq_swap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean)
-/
@[path]
lemma star_eq_swap
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {i j : ι} :
-- imply
  (i = R.star j) ↔ (j = R.star i) :=
-- proof
  ⟨fun h => by rw [← R.star_star j, h], fun h => by rw [h, R.star_star]⟩

end MultifusionRingDef

namespace MultifusionRingDef

/--
[sum_ite_star_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean)
-/
@[path]
lemma sum_ite_star_eq
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {i : ι}
  {g : ι → ℂ} :
-- imply
  (∑ j, if i = R.star j then g j else 0) = g (R.star i) := by
-- proof
  have : ∀ j, (if i = R.star j then g j else (0 : ℂ)) =
    (if j = R.star i then g j else 0) := by
    intro j
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd ((star_eq_swap R i j).mp h1) h2
    · exact absurd ((star_eq_swap R i j).mpr h2) h1
    · rfl
  simp_rw [this, sum_ite_eq', mem_univ, if_true]

end MultifusionRingDef

namespace MultifusionRingDef

/--
[sum_ite_mem_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean)
-/
@[path]
lemma sum_ite_mem_eq
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {S : Finset ι}
  {g : ι → ℂ} :
-- imply
  (∑ i : ι, if i ∈ S then g i else 0) = ∑ i ∈ S, g i := by
-- proof
  rw [← Finset.sum_filter]; congr 1; ext x; simp

end MultifusionRingDef

namespace MultifusionRingDef

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : MultifusionRingDef ι)
/--
[sum_I₀_mul_left_complex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean)
-/
@[path]
over `s` in the unit components gives the Kronecker delta in `j, k`. -/
lemma sum_I₀_mul_left_complex (j k : ι) :
  (∑ s ∈ R.I₀, (R.N s j k : ℂ)) = if j = k then 1 else 0 := by
  exact_mod_cast R.sum_I₀_mul_left j k

end MultifusionRingDef

namespace MultifusionRingDef

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : MultifusionRingDef ι)
/--
[sum_I₀_mul_right_complex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean)
-/
@[path]
over `s` in the unit components gives the Kronecker delta in `i, k`. -/
lemma sum_I₀_mul_right_complex (i k : ι) :
  (∑ s ∈ R.I₀, (R.N i s k : ℂ)) = if i = k then 1 else 0 := by
  exact_mod_cast R.sum_I₀_mul_right i k

end MultifusionRingDef

namespace MultifusionRingDef

/--
[assoc_complex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean)
-/
@[path]
lemma assoc_complex
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {i j k l : ι} :
-- imply
  (univ.sum fun m => (R.N i j m : ℂ) * (R.N m k l : ℂ)) = (univ.sum fun m => (R.N j k m : ℂ) * (R.N i m l : ℂ)) := by
-- proof
  exact_mod_cast R.assoc i j k l

end MultifusionRingDef

namespace MultifusionRingDef

/--
[mfGrMulC_one_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean)
-/
@[path]
lemma mfGrMulC_one_left
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {f : ι → ℂ} :
-- imply
  R.mfGrMulC (R.mfOneC) f = f := by
-- proof
  funext k; unfold mfGrMulC mfOneC
  simp_rw [ite_mul, one_mul, zero_mul]
  conv_lhs =>
    arg 2; ext i
    rw [show (∑ j, (if i ∈ R.I₀ then f j * (R.N i j k : ℂ) else 0)) =
      if i ∈ R.I₀ then ∑ j, f j * (R.N i j k : ℂ) else 0
      from by split_ifs <;> simp_all]
  rw [sum_ite_mem_eq R.I₀]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  simp_rw [R.sum_I₀_mul_left_complex, mul_ite, mul_one, mul_zero,
    sum_ite_eq', mem_univ, if_true]

end MultifusionRingDef

namespace MultifusionRingDef

/--
[mfGrMulC_one_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean)
-/
@[path]
lemma mfGrMulC_one_right
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {f : ι → ℂ} :
-- imply
  R.mfGrMulC f (R.mfOneC) = f := by
-- proof
  funext k; unfold mfGrMulC mfOneC
  simp_rw [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  conv_lhs =>
    arg 2; ext i; arg 2; ext j
    rw [show (if j ∈ R.I₀ then f i * (R.N i j k : ℂ) else 0) =
      f i * (if j ∈ R.I₀ then (R.N i j k : ℂ) else 0)
      from by split_ifs <;> simp]
  simp_rw [← Finset.mul_sum, sum_ite_mem_eq R.I₀]
  simp_rw [R.sum_I₀_mul_right_complex, mul_ite, mul_one, mul_zero,
    sum_ite_eq', mem_univ, if_true]

end MultifusionRingDef

namespace MultifusionRingDef

/--
[mf_inner_sum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean)
-/
@[path]
lemma mf_inner_sum_eq
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {a b c : ι → ℂ}
  {l i j k : ι} :
-- imply
  (∑ m : ι, a i * (b j * (c k * ((R.N i j m : ℂ) * (R.N m k l : ℂ))))) = (∑ q : ι, a i * (b j * (c k * ((R.N j k q : ℂ) * (R.N i q l : ℂ))))) := by
-- proof
  simp_rw [← Finset.mul_sum]
  congr 3
  exact R.assoc_complex i j k l

end MultifusionRingDef

namespace MultifusionRingDef

/--
[mfGrMulC_assoc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean)
-/
@[path]
lemma mfGrMulC_assoc
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {a b c : ι → ℂ} :
-- imply
  R.mfGrMulC (R.mfGrMulC a b) c = R.mfGrMulC a (R.mfGrMulC b c) := by
-- proof
  funext l; simp only [mfGrMulC]
  simp_rw [mul_assoc, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  trans (∑ i : ι, ∑ j, ∑ k, ∑ m,
    a i * (b j * (c k * ((R.N i j m : ℂ) * (R.N m k l : ℂ)))))
  · rw [Finset.sum_comm]
    conv_lhs => arg 2; ext _; rw [Finset.sum_comm]
    conv_lhs => arg 2; ext _; arg 2; ext _; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext _; rw [Finset.sum_comm]
    congr 1; ext i; congr 1; ext j; congr 1; ext k; congr 1; ext m; ring
  · conv_rhs => arg 2; ext _; rw [Finset.sum_comm]
    conv_rhs => arg 2; ext _; arg 2; ext _; rw [Finset.sum_comm]
    congr 1; ext i; congr 1; ext j; congr 1; ext k
    exact R.mf_inner_sum_eq a b c l i j k

end MultifusionRingDef

namespace MultifusionRingDef

/--
[mfGrMulC_left_distrib](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean)
-/
@[path]
lemma mfGrMulC_left_distrib
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {a b c : ι → ℂ} :
-- imply
  R.mfGrMulC a (fun k => b k + c k) = fun k => R.mfGrMulC a b k + R.mfGrMulC a c k := by
-- proof
  funext l; simp only [mfGrMulC]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]

end MultifusionRingDef

namespace MultifusionRingDef

/--
[mfGrMulC_right_distrib](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean)
-/
@[path]
lemma mfGrMulC_right_distrib
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {a b c : ι → ℂ} :
-- imply
  R.mfGrMulC (fun k => a k + b k) c = fun k => R.mfGrMulC a c k + R.mfGrMulC b c k := by
-- proof
  funext l; simp only [mfGrMulC]
  simp_rw [add_mul, Finset.sum_add_distrib]

end MultifusionRingDef

namespace MultifusionRingDef

/--
[mfGrMulC_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean)
-/
@[path]
lemma mfGrMulC_zero
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {a : ι → ℂ} :
-- imply
  R.mfGrMulC a (fun _ => 0) = fun _ => 0 := by
-- proof
  funext l; simp only [mfGrMulC]; simp

end MultifusionRingDef

namespace MultifusionRingDef

/--
[mfZeroC_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean)
-/
@[path]
lemma mfZeroC_mul
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {a : ι → ℂ} :
-- imply
  R.mfGrMulC (fun _ => 0) a = fun _ => 0 := by
-- proof
  funext l; simp only [mfGrMulC]; simp

end MultifusionRingDef

namespace MultifusionRingDef

/--
[mfGrMulC_smul_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean)
-/
@[path]
lemma mfGrMulC_smul_left
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {c : ℂ}
  {a b : ι → ℂ} :
-- imply
  R.mfGrMulC (fun k => c * a k) b = fun k => c * R.mfGrMulC a b k := by
-- proof
  funext l; simp only [mfGrMulC]
  simp_rw [mul_assoc, Finset.mul_sum]

end MultifusionRingDef

namespace MultifusionRingDef

/--
[mf_N_star_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean)
-/
@[path]
lemma mf_N_star_reverse
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {i j k : ι} :
-- imply
  R.N (R.star j) (R.star i) k = R.N i j (R.star k) := by
-- proof
  rw [R.star_anti (R.star j) (R.star i) k, R.star_star, R.star_star]

end MultifusionRingDef

namespace MultifusionRingDef

/--
[mfGrMulC_scalar_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean)
-/
@[path]
lemma mfGrMulC_scalar_left
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {c : ℂ}
  {f : ι → ℂ} :
-- imply
  R.mfGrMulC (fun k => if k ∈ R.I₀ then c else 0) f = fun k => c * R.mfGrMulC (R.mfOneC) f k := by
-- proof
  funext l; unfold mfGrMulC mfOneC
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.mul_sum]
  congr 1; ext i; rw [Finset.mul_sum]; congr 1; ext j
  split_ifs <;> ring

end MultifusionRingDef

namespace MultifusionRingDef

/--
[mfGrMulC_scalar_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean)
-/
@[path]
lemma mfGrMulC_scalar_right
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {c : ℂ}
  {f : ι → ℂ} :
-- imply
  R.mfGrMulC f (fun k => if k ∈ R.I₀ then c else 0) = fun k => c * R.mfGrMulC f (R.mfOneC) k := by
-- proof
  funext l; unfold mfGrMulC mfOneC
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.mul_sum]
  congr 1; ext i; rw [Finset.mul_sum]; congr 1; ext j
  split_ifs <;> ring

end MultifusionRingDef

namespace MultifusionRingDef

/--
[mfGrTraceC_mul_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean)
-/
@[path]
lemma mfGrTraceC_mul_eq
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {a b : ι → ℂ} :
-- imply
  R.mfGrTraceC (R.mfGrMulC a b) = ∑ i, a i * b (R.star i) := by
-- proof
  unfold mfGrTraceC mfGrMulC
  rw [Finset.sum_comm]
  congr 1; ext i
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext j
    rw [show ∑ x ∈ R.I₀, a i * b j * (R.N i j x : ℂ) =
      a i * b j * ∑ x ∈ R.I₀, (R.N i j x : ℂ)
      from by rw [Finset.mul_sum]]
  have hdual : ∀ j, (∑ k ∈ R.I₀, (R.N i j k : ℂ)) = if i = R.star j then 1 else 0 := by
    intro j; exact_mod_cast R.duality_trace i j
  simp_rw [hdual, mul_ite, mul_one, mul_zero]
  exact sum_ite_star_eq R i (fun j => a i * b j)

end MultifusionRingDef

namespace MultifusionRingDef

/--
[mf_trace_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean)
-/
@[path]
lemma mf_trace_comm
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {a b : ι → ℂ} :
-- imply
  R.mfGrTraceC (R.mfGrMulC a b) = R.mfGrTraceC (R.mfGrMulC b a) := by
-- proof
  rw [mfGrTraceC_mul_eq, mfGrTraceC_mul_eq]
  rw [← Equiv.sum_comp R.mfStarEquiv (fun x => a x * b (R.star x))]
  simp only [mfStarEquiv, Equiv.coe_fn_mk, R.star_star]
  congr 1; ext x; ring

end MultifusionRingDef

namespace MultifusionRingDef

/--
[mf_trace_star_mul_eq_sum_normSq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean)
-/
@[path]
lemma mf_trace_star_mul_eq_sum_normSq
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {a : ι → ℂ} :
-- imply
  R.mfGrTraceC (R.mfGrMulC a (R.mfGrStarC a)) = ∑ i : ι, (Complex.normSq (a i) : ℂ) := by
-- proof
  rw [mfGrTraceC_mul_eq]
  unfold mfGrStarC
  simp_rw [R.star_star]
  congr 1; ext i; rw [mul_conj]

end MultifusionRingDef

namespace MultifusionRingDef

/--
[mf_trace_star_mul_re](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean)
-/
@[path]
lemma mf_trace_star_mul_re
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {a : ι → ℂ} :
-- imply
  (R.mfGrTraceC (R.mfGrMulC a (R.mfGrStarC a))).re = ∑ i : ι, Complex.normSq (a i) := by
-- proof
  rw [mf_trace_star_mul_eq_sum_normSq]
  simp [Complex.ofReal_re]

end MultifusionRingDef

namespace MultifusionRingDef

/--
[mf_trace_pos_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean)
-/
@[path]
lemma mf_trace_pos_def
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {a : ι → ℂ}
-- given
  (ha : a ≠ 0) :
-- imply
  0 < (R.mfGrTraceC (R.mfGrMulC a (R.mfGrStarC a))).re := by
-- proof
  rw [mf_trace_star_mul_re]
  apply (Finset.sum_pos_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (a i))).mpr
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h; push Not at h; exact ha (funext h)
  exact ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩
end


namespace MultifusionRingDef

/--
[mf_complexified_semisimple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean)
-/
@[path]
lemma mf_complexified_semisimple
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι} :
-- imply
  IsSemisimpleRing (MfGrRingOfC R) :=
-- proof
  @StarAlgWithTrace.starAlgWithTrace_isSemisimple R.mfGrStarAlgWithTrace
    MfGrRingOfC.instFiniteDimensional

end MultifusionRingDef

/--
[sum_I](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean)
-/
@[path]
private lemma sum_I_eq
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {j k : ι} :
-- imply
  (∑ s ∈ R.I₀, (R.N s j k : ℂ)) = if j = k then 1 else 0 := by
-- proof
  apply MultifusionRingDef.sum_I R j k

/--
[sum_I](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean)
-/
@[path]
private lemma sum_I_eq_2
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {i k : ι} :
-- imply
  (∑ s ∈ R.I₀, (R.N i s k : ℂ)) = if i = k then 1 else 0 := by
-- proof
  apply MultifusionRingDef.sum_I R i k

/--
[coeff_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean)
-/
@[path]
private lemma coeff_zero_eq
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {k : ι} :
-- imply
  (0 : MfGrRingOfC R).coeff k = 0 := by
-- proof
  apply MfGrRingOfC.coeff_zero k

/--
[coeff_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean)
-/
@[path]
private lemma coeff_one_eq
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {k : ι} :
-- imply
  (1 : MfGrRingOfC R).coeff k = if k ∈ R.I₀ then 1 else 0 := by
-- proof
  apply MfGrRingOfC.coeff_one k

/--
[coeff_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean)
-/
@[path]
private lemma coeff_add_eq
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {a b : MfGrRingOfC R}
  {k : ι} :
-- imply
  (a + b).coeff k = a.coeff k + b.coeff k := by
-- proof
  apply MfGrRingOfC.coeff_add a b k

/--
[coeff_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean)
-/
@[path]
private lemma coeff_neg_eq
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {a : MfGrRingOfC R}
  {k : ι} :
-- imply
  (-a).coeff k = -a.coeff k := by
-- proof
  apply MfGrRingOfC.coeff_neg a k

/--
[coeff_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean)
-/
@[path]
private lemma coeff_sub_eq
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {a b : MfGrRingOfC R}
  {k : ι} :
-- imply
  (a - b).coeff k = a.coeff k - b.coeff k := by
-- proof
  apply MfGrRingOfC.coeff_sub a b k


-- created on 2026-10-23
