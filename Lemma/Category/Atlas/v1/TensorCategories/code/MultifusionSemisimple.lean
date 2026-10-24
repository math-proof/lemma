import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.MultifusionSemisimple
open Finset Complex MultifusionRingDef MultifusionRingDef.MfGrRingOfC


namespace MultifusionRingDef

/--
[mf_assoc_complex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MultifusionSemisimple.lean)
-/
@[path]
lemma mf_assoc_complex
  [DecidableEq ι]
  [Fintype ι]
  {M : MultifusionRingDef ι}
  {i j k l : ι} :
-- imply
  (univ.sum fun m => (M.N i j m : ℂ) * (M.N m k l : ℂ)) = (univ.sum fun m => (M.N j k m : ℂ) * (M.N i m l : ℂ)) := by
-- proof
  exact_mod_cast M.assoc i j k l

end MultifusionRingDef

namespace MultifusionRingDef

/--
[mfGrMulC_left_distrib](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MultifusionSemisimple.lean)
-/
@[path]
lemma mfGrMulC_left_distrib
  [DecidableEq ι]
  [Fintype ι]
  {M : MultifusionRingDef ι}
  {a b c : ι → ℂ} :
-- imply
  M.mfGrMulC a (fun k => b k + c k) = fun k => M.mfGrMulC a b k + M.mfGrMulC a c k := by
-- proof
  funext l; simp only [mfGrMulC]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]

end MultifusionRingDef

namespace MultifusionRingDef

/--
[mfGrMulC_right_distrib](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MultifusionSemisimple.lean)
-/
@[path]
lemma mfGrMulC_right_distrib
  [DecidableEq ι]
  [Fintype ι]
  {M : MultifusionRingDef ι}
  {a b c : ι → ℂ} :
-- imply
  M.mfGrMulC (fun k => a k + b k) c = fun k => M.mfGrMulC a c k + M.mfGrMulC b c k := by
-- proof
  funext l; simp only [mfGrMulC]
  simp_rw [add_mul, Finset.sum_add_distrib]

end MultifusionRingDef

namespace MultifusionRingDef

/--
[mfGrMulC_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MultifusionSemisimple.lean)
-/
@[path]
lemma mfGrMulC_zero
  [DecidableEq ι]
  [Fintype ι]
  {M : MultifusionRingDef ι}
  {a : ι → ℂ} :
-- imply
  M.mfGrMulC a (fun _ => 0) = fun _ => 0 := by
-- proof
  funext l; simp only [mfGrMulC]; simp

end MultifusionRingDef

namespace MultifusionRingDef

/--
[mfGrZeroC_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MultifusionSemisimple.lean)
-/
@[path]
lemma mfGrZeroC_mul
  [DecidableEq ι]
  [Fintype ι]
  {M : MultifusionRingDef ι}
  {a : ι → ℂ} :
-- imply
  M.mfGrMulC (fun _ => 0) a = fun _ => 0 := by
-- proof
  funext l; simp only [mfGrMulC]; simp

end MultifusionRingDef

namespace MultifusionRingDef

/--
[mfGrMulC_scalar_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MultifusionSemisimple.lean)
-/
@[path]
lemma mfGrMulC_scalar_left
  [DecidableEq ι]
  [Fintype ι]
  {M : MultifusionRingDef ι}
  {c : ℂ}
  {f : ι → ℂ} :
-- imply
  M.mfGrMulC (fun k => if k ∈ M.I₀ then c else 0) f = fun k => c * M.mfGrMulC (fun k => if k ∈ M.I₀ then 1 else 0) f k := by
-- proof
  funext l; unfold mfGrMulC
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.mul_sum]
  congr 1; ext i; rw [Finset.mul_sum]; congr 1; ext j
  split <;> ring

end MultifusionRingDef

namespace MultifusionRingDef

/--
[mfGrMulC_scalar_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MultifusionSemisimple.lean)
-/
@[path]
lemma mfGrMulC_scalar_right
  [DecidableEq ι]
  [Fintype ι]
  {M : MultifusionRingDef ι}
  {c : ℂ}
  {f : ι → ℂ} :
-- imply
  M.mfGrMulC f (fun k => if k ∈ M.I₀ then c else 0) = fun k => c * M.mfGrMulC f (fun k => if k ∈ M.I₀ then 1 else 0) k := by
-- proof
  funext l; unfold mfGrMulC
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.mul_sum]
  congr 1; ext i; rw [Finset.mul_sum]; congr 1; ext j
  split <;> ring

end MultifusionRingDef

/--
[coeff_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MultifusionSemisimple.lean)
-/
@[path]
private lemma coeff_zero_eq
  [DecidableEq ι]
  [Fintype ι]
  {M : MultifusionRingDef ι}
  {M : MultifusionRingDef ι}
  {k : ι} :
-- imply
  (0 : MfGrRingOfC M).coeff k = 0 := by
-- proof
  apply MultifusionRingDef.MfGrRingOfC.coeff_zero M k

/--
[coeff_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MultifusionSemisimple.lean)
-/
@[path]
private lemma coeff_one_eq
  [DecidableEq ι]
  [Fintype ι]
  {M : MultifusionRingDef ι}
  {M : MultifusionRingDef ι}
  {k : ι} :
-- imply
  (1 : MfGrRingOfC M).coeff k = if k ∈ M.I₀ then 1 else 0 := by
-- proof
  apply MultifusionRingDef.MfGrRingOfC.coeff_one M k

/--
[coeff_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MultifusionSemisimple.lean)
-/
@[path]
private lemma coeff_add_eq
  [DecidableEq ι]
  [Fintype ι]
  {M : MultifusionRingDef ι}
  {M : MultifusionRingDef ι}
  {a b : MfGrRingOfC M}
  {k : ι} :
-- imply
  (a + b).coeff k = a.coeff k + b.coeff k := by
-- proof
  apply MultifusionRingDef.MfGrRingOfC.coeff_add M a b k

/--
[coeff_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MultifusionSemisimple.lean)
-/
@[path]
private lemma coeff_neg_eq
  [DecidableEq ι]
  [Fintype ι]
  {M : MultifusionRingDef ι}
  {M : MultifusionRingDef ι}
  {a : MfGrRingOfC M}
  {k : ι} :
-- imply
  (-a).coeff k = -a.coeff k := by
-- proof
  apply MultifusionRingDef.MfGrRingOfC.coeff_neg M a k

/--
[coeff_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MultifusionSemisimple.lean)
-/
@[path]
private lemma coeff_sub_eq
  [DecidableEq ι]
  [Fintype ι]
  {M : MultifusionRingDef ι}
  {M : MultifusionRingDef ι}
  {a b : MfGrRingOfC M}
  {k : ι} :
-- imply
  (a - b).coeff k = a.coeff k - b.coeff k := by
-- proof
  apply MultifusionRingDef.MfGrRingOfC.coeff_sub M a b k


-- created on 2026-10-23
