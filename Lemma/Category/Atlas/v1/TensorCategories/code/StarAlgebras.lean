import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.StarAlgebras
open Finset Complex MultifusionRingDef


/--
[prop_1_43_2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebras.lean)
-/
@[path]
lemma prop_1_43_2
  {B : StarAlgWithTrace}
  [FiniteDimensional ℂ B.carrier] :
-- imply
  @IsSemisimpleRing B.carrier B.instRing :=
-- proof
  B.starAlgWithTrace_isSemisimple

/--
[Proposition_1_43_2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebras.lean)
-/
@[path]
lemma Proposition_1_43_2
  {B : StarAlgWithTrace}
  [FiniteDimensional ℂ B.carrier] :
-- imply
  @IsSemisimpleRing B.carrier B.instRing :=
-- proof
  B.starAlgWithTrace_isSemisimple
set_option maxHeartbeats 400000
open Finset Complex
namespace MultifusionRingDef
variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : MultifusionRingDef ι)

namespace MultifusionRingDef

/--
[duality_trace_cast](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebras.lean)
-/
@[path]
lemma duality_trace_cast
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {i j : ι} :
-- imply
  (∑ k ∈ R.I₀, (R.N i j k : ℂ)) = if i = R.star j then 1 else 0 := by
-- proof
  have h := R.duality_trace i j
  have : (∑ k ∈ R.I₀, (R.N i j k : ℂ)) = ((∑ k ∈ R.I₀, R.N i j k : ℕ) : ℂ) := by
    push_cast; rfl
  rw [this, h]; split_ifs <;> simp

end MultifusionRingDef

namespace MultifusionRingDef

/--
[trace_mul_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebras.lean)
-/
@[path]
lemma trace_mul_eq
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {f g : ι → ℂ} :
-- imply
  R.grTraceC (R.grMulC f g) = ∑ j : ι, f (R.star j) * g j := by
-- proof
  unfold grTraceC grMulC
  rw [Finset.sum_comm (s := R.I₀)]
  simp_rw [Finset.sum_comm (s := R.I₀) (t := univ)]
  simp_rw [← Finset.mul_sum, duality_trace_cast]
  simp_rw [show ∀ i j : ι, (i = R.star j) ↔ (j = R.star i) from
    fun i j => ⟨fun h => by rw [h, R.star_star], fun h => by rw [h, R.star_star]⟩]
  simp_rw [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true]
  rw [← Equiv.sum_comp R.starEquivC]
  simp only [starEquivC, Equiv.coe_fn_mk, R.star_star]

end MultifusionRingDef

namespace MultifusionRingDef

/--
[trace_comm_based](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebras.lean)
-/
@[path]
lemma trace_comm_based
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {a b : ι → ℂ} :
-- imply
  R.grTraceC (R.grMulC a b) = R.grTraceC (R.grMulC b a) := by
-- proof
  rw [trace_mul_eq, trace_mul_eq]
  rw [← Equiv.sum_comp R.starEquivC (fun j => a (R.star j) * b j)]
  simp only [starEquivC, Equiv.coe_fn_mk, R.star_star]
  congr 1; ext x; ring

end MultifusionRingDef

namespace MultifusionRingDef

/--
[trace_star_mul_eq_sum_normSq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebras.lean)
-/
@[path]
lemma trace_star_mul_eq_sum_normSq
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {a : ι → ℂ} :
-- imply
  R.grTraceC (R.grMulC a (R.grStarC a)) = ∑ i : ι, (Complex.normSq (a i) : ℂ) := by
-- proof
  rw [trace_mul_eq]
  simp only [grStarC]
  simp_rw [mul_conj]
  rw [← Equiv.sum_comp R.starEquivC (fun j => (Complex.normSq (a j) : ℂ))]
  simp only [starEquivC, Equiv.coe_fn_mk]

end MultifusionRingDef

namespace MultifusionRingDef

/--
[trace_star_mul_re](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebras.lean)
-/
@[path]
lemma trace_star_mul_re
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {a : ι → ℂ} :
-- imply
  (R.grTraceC (R.grMulC a (R.grStarC a))).re = ∑ i : ι, Complex.normSq (a i) := by
-- proof
  rw [trace_star_mul_eq_sum_normSq]
  simp [Complex.ofReal_re]

end MultifusionRingDef

namespace MultifusionRingDef

/--
[trace_pos_def_based](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebras.lean)
-/
@[path]
lemma trace_pos_def_based
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {a : ι → ℂ}
-- given
  (ha : a ≠ 0) :
-- imply
  0 < (R.grTraceC (R.grMulC a (R.grStarC a))).re := by
-- proof
  rw [trace_star_mul_re]
  apply Finset.sum_pos' (fun i _ => Complex.normSq_nonneg (a i))
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h; push Not at h; exact ha (funext h)
  exact ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩

end MultifusionRingDef

namespace MultifusionRingDef

/--
[grStarC_involution](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebras.lean)
-/
@[path]
lemma grStarC_involution
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {f : ι → ℂ} :
-- imply
  R.grStarC (R.grStarC f) = f := by
-- proof
  ext i
  simp [grStarC, R.star_star]

end MultifusionRingDef

namespace MultifusionRingDef

/--
[grStarC_anti_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebras.lean)
-/
@[path]
lemma grStarC_anti_mul
  [DecidableEq ι]
  [Fintype ι]
  {R : MultifusionRingDef ι}
  {f g : ι → ℂ} :
-- imply
  R.grStarC (R.grMulC f g) = R.grMulC (R.grStarC g) (R.grStarC f) := by
-- proof
  ext k
  simp only [grStarC, grMulC]
  simp_rw [map_sum, map_mul, map_natCast]
  simp_rw [show ∀ i j, (R.N i j (R.star k) : ℂ) = (R.N (R.star j) (R.star i) k : ℂ)
    from fun i j => by congr 1; rw [R.star_anti]; congr 1; exact (R.star_star k)]
  rw [Finset.sum_comm]
  conv_lhs => rw [← Equiv.sum_comp R.starEquivC]
  simp only [starEquivC, Equiv.coe_fn_mk, R.star_star]
  congr 1; ext j
  conv_lhs => rw [← Equiv.sum_comp R.starEquivC]
  simp only [starEquivC, Equiv.coe_fn_mk, R.star_star]
  congr 1; ext i; ring

end MultifusionRingDef


-- created on 2026-10-23
