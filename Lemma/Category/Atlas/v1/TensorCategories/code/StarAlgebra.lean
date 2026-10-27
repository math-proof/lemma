import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.TensorCategories.code.StarAlgebra
open Finset Complex StarAlgWithTrace FusionRing MultifusionRingDef


namespace StarAlgWithTrace

/--
[mul_star_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebra.lean)
-/
@[path]
lemma mul_star_ne_zero
  {B : StarAlgWithTrace}
  {a : B.carrier}
-- given
  (ha : a ≠ 0) :
-- imply
  a * star a ≠ 0 := by
-- proof
  intro h
  have h1 := B.trace_pos_def a ha
  rw [h, map_zero] at h1
  simp at h1

end StarAlgWithTrace

namespace StarAlgWithTrace

/--
[star_mul_star_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebra.lean)
-/
@[path]
lemma star_mul_star_self
  {B : StarAlgWithTrace}
  {a : B.carrier} :
-- imply
  star (a * star a) = a * star a := by
-- proof
  rw [star_mul, star_star]

end StarAlgWithTrace

namespace StarAlgWithTrace

/--
[star_pow_of_star_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebra.lean)
-/
@[path]
lemma star_pow_of_star_self
  {B : StarAlgWithTrace}
  {a : B.carrier}
  {n : ℕ}
-- given
  (hstar : star a = a) :
-- imply
  star (a ^ n) = a ^ n := by
-- proof
  rw [star_pow, hstar]

end StarAlgWithTrace

namespace StarAlgWithTrace

/--
[sq_ne_zero_of_star_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebra.lean)
-/
@[path]
lemma sq_ne_zero_of_star_self
  {B : StarAlgWithTrace}
  {a : B.carrier}
-- given
  (ha : a ≠ 0)
  (hstar : star a = a) :
-- imply
  a ^ 2 ≠ 0 := by
-- proof
  rw [sq, show a * a = a * star a from by rw [hstar]]
  exact B.mul_star_ne_zero a ha

end StarAlgWithTrace

namespace StarAlgWithTrace

/--
[jacobson_eq_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebra.lean)
-/
@[path]
lemma jacobson_eq_bot
  {B : StarAlgWithTrace}
  [FiniteDimensional ℂ B.carrier] :
-- imply
  Ring.jacobson B.carrier = ⊥ := by
-- proof
  rw [eq_bot_iff]
  intro a ha
  rw [Submodule.mem_bot]
  by_contra h
  set J := Ring.jacobson B.carrier with hJ_def
  have hJ_nilp := IsArtinianRing.isNilpotent_jacobson_bot (R := B.carrier)
  rw [Ideal.jacobson_bot] at hJ_nilp
  obtain ⟨n, hn⟩ := hJ_nilp
  set c := a * star a with hc_def
  have hc_mem : c ∈ J := J.mul_mem_right (star a) ha
  have hc_ne : c ≠ 0 := B.mul_star_ne_zero a h
  have hc_star : star c = c := B.star_mul_star_self a
  have key : ∀ k : ℕ, c ^ (2 ^ k) ≠ 0 := by
    intro k
    induction k with
    | zero => simpa using hc_ne
    | succ k ih =>
      rw [pow_succ, pow_mul]
      exact B.sq_ne_zero_of_star_self ih (B.star_pow_of_star_self hc_star _)
  have hmem : c ^ (2 ^ n) ∈ J ^ (2 ^ n) := Ideal.pow_mem_pow hc_mem _
  have hzero : J ^ (2 ^ n) = ⊥ := by
    rw [eq_bot_iff]
    exact (Ideal.pow_le_pow_right Nat.lt_two_pow_self.le).trans (le_of_eq hn)
  rw [hzero] at hmem
  exact key n ((Submodule.mem_bot _).mp hmem)

end StarAlgWithTrace

namespace StarAlgWithTrace

/--
[starAlgWithTrace_isSemisimple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebra.lean)
-/
@[path]
lemma starAlgWithTrace_isSemisimple
  {B : StarAlgWithTrace}
  [FiniteDimensional ℂ B.carrier] :
-- imply
  @IsSemisimpleRing B.carrier B.instRing := by
-- proof
  rwa [IsArtinianRing.isSemisimpleRing_iff_jacobson]
end StarAlgWithTrace


namespace FusionRing

/--
[trace_comm_grC](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebra.lean)
-/
@[path]
lemma trace_comm_grC
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {a b : ι → ℂ} :
-- imply
  R.grTraceC (R.grMulC a b) = R.grTraceC (R.grMulC b a) := by
-- proof
  unfold grTraceC grMulC
  simp_rw [R.duality, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true]
  rw [← Equiv.sum_comp R.starEquivC (fun x => a x * b (R.star x))]
  simp only [starEquivC, Equiv.coe_fn_mk, R.star_star]
  congr 1; ext x; ring

end FusionRing

namespace FusionRing

/--
[trace_star_mul_eq_sum_normSq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebra.lean)
-/
@[path]
lemma trace_star_mul_eq_sum_normSq
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {a : ι → ℂ} :
-- imply
  R.grTraceC (R.grMulC a (R.grStarC a)) = ∑ i : ι, (Complex.normSq (a i) : ℂ) := by
-- proof
  unfold grTraceC grMulC grStarC
  simp_rw [R.duality, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true, R.star_star]
  congr 1; ext i; rw [mul_conj]

end FusionRing

namespace FusionRing

/--
[trace_star_mul_re](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebra.lean)
-/
@[path]
lemma trace_star_mul_re
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {a : ι → ℂ} :
-- imply
  (R.grTraceC (R.grMulC a (R.grStarC a))).re = ∑ i : ι, Complex.normSq (a i) := by
-- proof
  rw [trace_star_mul_eq_sum_normSq]
  simp [Complex.ofReal_re]

end FusionRing

namespace FusionRing

/--
[trace_pos_def_grC](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebra.lean)
-/
@[path]
lemma trace_pos_def_grC
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {a : ι → ℂ}
-- given
  (ha : a ≠ 0) :
-- imply
  0 < (R.grTraceC (R.grMulC a (R.grStarC a))).re := by
-- proof
  rw [trace_star_mul_re]
  apply (Finset.sum_pos_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (a i))).mpr
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h; push Not at h; exact ha (funext h)
  exact ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩

end FusionRing

namespace FusionRing

/--
[Proposition_1_43_4_fusion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebra.lean)
-/
@[path]
lemma Proposition_1_43_4_fusion
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι} :
-- imply
  (∀ f : ι → ℂ, R.grStarC (R.grStarC f) = f) ∧ (∀ a b : ι → ℂ, R.grTraceC (R.grMulC a b) = R.grTraceC (R.grMulC b a)) ∧ (∀ a : ι → ℂ, a ≠ 0 → 0 < (R.grTraceC (R.grMulC a (R.grStarC a))).re) := by
-- proof
  exact ⟨by
    intro f; ext i; simp [grStarC, R.star_star],
    R.trace_comm_grC,
    R.trace_pos_def_grC⟩
end


namespace MultifusionRingDef

/--
[grStarC'_invol](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebra.lean)
-/
@[path]
lemma grStarC'_invol
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {f : ι → ℂ} :
-- imply
  R.grStarC' (R.grStarC' f) = f := by
-- proof
  ext i; simp [grStarC', R.star_star]

end MultifusionRingDef

namespace MultifusionRingDef

/--
[grStarC'_anti_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebra.lean)
-/
@[path]
lemma grStarC'_anti_mul
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {f g : ι → ℂ} :
-- imply
  R.grStarC' (R.grMulC' f g) = R.grMulC' (R.grStarC' g) (R.grStarC' f) := by
-- proof
  ext k
  simp only [grStarC', grMulC']
  rw [map_sum]
  simp_rw [map_sum, map_mul, starRingEnd_apply, star_natCast]
  conv_lhs =>
    arg 2; ext i; arg 2; ext j
    rw [R.star_anti i j (R.star k), R.star_star k]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext j
    rw [← Equiv.sum_comp R.starEquivC']
  rw [← Equiv.sum_comp R.starEquivC']
  simp only [starEquivC', Equiv.coe_fn_mk, R.star_star]
  congr 1; ext i; congr 1; ext j; ring

end MultifusionRingDef

namespace MultifusionRingDef

/--
[trace_star_mul_eq_sum_normSq'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebra.lean)
-/
@[path]
lemma trace_star_mul_eq_sum_normSq'
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {a : ι → ℂ} :
-- imply
  R.grTraceC' (R.grMulC' a (R.grStarC' a)) = ∑ i : ι, (Complex.normSq (a i) : ℂ) := by
-- proof
  simp only [grTraceC', grMulC', grStarC']
  simp_rw [Finset.sum_comm (s := R.I₀)]
  simp_rw [← Finset.mul_sum]
  have cast_sum : ∀ i j, (∑ k ∈ R.I₀, (R.N i j k : ℂ)) =
    ((∑ k ∈ R.I₀, R.N i j k : ℕ) : ℂ) := by
    intros; push_cast; rfl
  simp_rw [cast_sum, R.duality_trace, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    mul_ite, mul_one, mul_zero]
  conv_lhs =>
    arg 2; ext i
    rw [← Equiv.sum_comp R.starEquivC']
  simp only [starEquivC', Equiv.coe_fn_mk, R.star_star]
  simp_rw [sum_ite_eq, mem_univ, if_true]
  congr 1; ext i; rw [mul_conj]

end MultifusionRingDef

namespace MultifusionRingDef

/--
[trace_star_mul_re'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebra.lean)
-/
@[path]
lemma trace_star_mul_re'
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {a : ι → ℂ} :
-- imply
  (R.grTraceC' (R.grMulC' a (R.grStarC' a))).re = ∑ i : ι, Complex.normSq (a i) := by
-- proof
  rw [trace_star_mul_eq_sum_normSq']
  simp [Complex.ofReal_re]

end MultifusionRingDef

namespace MultifusionRingDef

/--
[trace_comm_grC'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebra.lean)
-/
@[path]
lemma trace_comm_grC'
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {a b : ι → ℂ} :
-- imply
  R.grTraceC' (R.grMulC' a b) = R.grTraceC' (R.grMulC' b a) := by
-- proof
  simp only [grTraceC', grMulC']
  simp_rw [Finset.sum_comm (s := R.I₀)]
  simp_rw [← Finset.mul_sum]
  have cast_sum : ∀ i j, (∑ k ∈ R.I₀, (R.N i j k : ℂ)) =
    ((∑ k ∈ R.I₀, R.N i j k : ℕ) : ℂ) := by
    intros; push_cast; rfl
  simp_rw [cast_sum, R.duality_trace, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    mul_ite, mul_one, mul_zero]
  conv_lhs =>
    arg 2; ext i
    rw [← Equiv.sum_comp R.starEquivC']
  simp only [starEquivC', Equiv.coe_fn_mk, R.star_star]
  simp_rw [sum_ite_eq, mem_univ, if_true]
  conv_rhs =>
    arg 2; ext i
    rw [← Equiv.sum_comp R.starEquivC']
  simp only [starEquivC', Equiv.coe_fn_mk, R.star_star]
  simp_rw [sum_ite_eq, mem_univ, if_true]
  rw [← Equiv.sum_comp R.starEquivC']
  simp only [starEquivC', Equiv.coe_fn_mk, R.star_star]
  congr 1; ext x; ring

end MultifusionRingDef

namespace MultifusionRingDef

/--
[trace_pos_def_grC'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebra.lean)
-/
@[path]
lemma trace_pos_def_grC'
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {a : ι → ℂ}
-- given
  (ha : a ≠ 0) :
-- imply
  0 < (R.grTraceC' (R.grMulC' a (R.grStarC' a))).re := by
-- proof
  rw [trace_star_mul_re']
  apply (Finset.sum_pos_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (a i))).mpr
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h; push Not at h; exact ha (funext h)
  exact ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩

end MultifusionRingDef

/--
[Proposition_1_43_4](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebra.lean)
-/
@[path]
private lemma Proposition_1_43_4_eq
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι} :
-- imply
  (∀ f : ι → ℂ, R.grStarC' (R.grStarC' f) = f) ∧ (∀ f g : ι → ℂ, R.grStarC' (R.grMulC' f g) = R.grMulC' (R.grStarC' g) (R.grStarC' f)) ∧ (∀ a b : ι → ℂ, R.grTraceC' (R.grMulC' a b) = R.grTraceC' (R.grMulC' b a)) ∧ (∀ a : ι → ℂ, a ≠ 0 → 0 < (R.grTraceC' (R.grMulC' a (R.grStarC' a))).re) := by
-- proof
  apply MultifusionRingDef.Proposition_1_43_4 R


-- created on 2026-10-23
