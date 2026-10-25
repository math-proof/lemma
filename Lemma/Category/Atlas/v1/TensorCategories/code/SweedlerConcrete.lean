import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.TensorCategories.code.SweedlerConcrete.Part4
open SweedlerH4


namespace SweedlerH4

/--
[gen_g_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerConcrete.lean)
-/
@[path]
lemma gen_g_sq
  [Field k] :
-- imply
  (gen_g : SweedlerH4 k) * gen_g = 1 := by
-- proof
  ext m; simp only [gen_g, coeff_mul, coeff_e, coeff_one, Fin4_sum, basisMul]
  fin_cases m <;> simp

end SweedlerH4

namespace SweedlerH4

/--
[gen_x_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerConcrete.lean)
-/
@[path]
lemma gen_x_sq
  [Field k] :
-- imply
  (gen_x : SweedlerH4 k) * gen_x = 0 := by
-- proof
  ext m; simp only [gen_x, coeff_mul, coeff_e, coeff_zero', Fin4_sum, basisMul]
  fin_cases m <;> simp

end SweedlerH4

/--
[coeff_zero'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerConcrete.lean)
-/
@[path]
private lemma coeff_zero'_eq
  [Field k]
  {i : Fin 4} :
-- imply
  (0 : SweedlerH4 k).coeff i = 0 := by
-- proof
  apply SweedlerH4.coeff_zero' i

/--
[coeff_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerConcrete.lean)
-/
@[path]
private lemma coeff_add_eq
  [Field k]
  {a b : SweedlerH4 k}
  {i : Fin 4} :
-- imply
  (a + b).coeff i = a.coeff i + b.coeff i := by
-- proof
  apply SweedlerH4.coeff_add a b i

/--
[coeff_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerConcrete.lean)
-/
@[path]
private lemma coeff_neg_eq
  [Field k]
  {a : SweedlerH4 k}
  {i : Fin 4} :
-- imply
  (-a).coeff i = -a.coeff i := by
-- proof
  apply SweedlerH4.coeff_neg a i

/--
[coeff_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerConcrete.lean)
-/
@[path]
private lemma coeff_sub_eq
  [Field k]
  {a b : SweedlerH4 k}
  {i : Fin 4} :
-- imply
  (a - b).coeff i = a.coeff i - b.coeff i := by
-- proof
  apply SweedlerH4.coeff_sub a b i

/--
[coeff_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerConcrete.lean)
-/
@[path]
private lemma coeff_smul_eq
  [Field k]
  {r : k}
  {a : SweedlerH4 k}
  {i : Fin 4} :
-- imply
  (r • a).coeff i = r * a.coeff i := by
-- proof
  apply SweedlerH4.coeff_smul r a i

/--
[coeff_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerConcrete.lean)
-/
@[path]
private lemma coeff_mul_eq
  [Field k]
  {a b : SweedlerH4 k}
  {m : Fin 4} :
-- imply
  (a * b).coeff m = ∑ i : Fin 4, ∑ j : Fin 4, a.coeff i * b.coeff j * basisMul i j m := by
-- proof
  apply SweedlerH4.coeff_mul a b m

/--
[coeff_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerConcrete.lean)
-/
@[path]
private lemma coeff_one_eq
  [Field k]
  {m : Fin 4} :
-- imply
  (1 : SweedlerH4 k).coeff m = if m = 0 then 1 else 0 := by
-- proof
  apply SweedlerH4.coeff_one m

/--
[coeff_natCast](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerConcrete.lean)
-/
@[path]
private lemma coeff_natCast_eq
  [Field k]
  {n : ℕ}
  {m : Fin 4} :
-- imply
  (n : SweedlerH4 k).coeff m = if m = 0 then (n : k) else 0 := by
-- proof
  apply SweedlerH4.coeff_natCast n m

/--
[coeff_intCast](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerConcrete.lean)
-/
@[path]
private lemma coeff_intCast_eq
  [Field k]
  {n : ℤ}
  {m : Fin 4} :
-- imply
  (n : SweedlerH4 k).coeff m = if m = 0 then (n : k) else 0 := by
-- proof
  apply SweedlerH4.coeff_intCast n m

/--
[Fin4_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerConcrete.lean)
-/
@[path]
private lemma Fin4_sum_eq
  [Field k]
  {f : Fin 4 → k} :
-- imply
  ∑ i : Fin 4, f i = f 0 + f 1 + f 2 + f 3 := by
-- proof
  apply SweedlerH4.Fin4_sum f

/--
[finrank_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerConcrete.lean)
-/
@[path]
private lemma finrank_eq_eq
  [Field k] :
-- imply
  Module.finrank k (SweedlerH4 k) = 4 := by
-- proof
  apply SweedlerH4.finrank_eq

/--
[coeff_e](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerConcrete.lean)
-/
@[path]
private lemma coeff_e_eq
  [Field k]
  {i j : Fin 4} :
-- imply
  (e i : SweedlerH4 k).coeff j = if i = j then 1 else 0 := by
-- proof
  apply SweedlerH4.coeff_e i j

/--
[coeff_gen_g](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerConcrete.lean)
-/
@[path]
private lemma coeff_gen_g_eq
  [Field k]
  {j : Fin 4} :
-- imply
  (gen_g : SweedlerH4 k).coeff j = if (1 : Fin 4) = j then 1 else 0 := by
-- proof
  apply SweedlerH4.coeff_gen_g j

/--
[coeff_gen_x](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerConcrete.lean)
-/
@[path]
private lemma coeff_gen_x_eq
  [Field k]
  {j : Fin 4} :
-- imply
  (gen_x : SweedlerH4 k).coeff j = if (2 : Fin 4) = j then 1 else 0 := by
-- proof
  apply SweedlerH4.coeff_gen_x j

/--
[gen_gx_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerConcrete.lean)
-/
@[path]
private lemma gen_gx_comm_eq
  [Field k] :
-- imply
  (gen_g : SweedlerH4 k) * gen_x = -(gen_x * gen_g) := by
-- proof
  apply SweedlerH4.gen_gx_comm

/--
[gen_g_mul_x](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerConcrete.lean)
-/
@[path]
private lemma gen_g_mul_x_eq
  [Field k] :
-- imply
  (gen_g : SweedlerH4 k) * gen_x = e 3 := by
-- proof
  apply SweedlerH4.gen_g_mul_x

/--
[e_zero_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerConcrete.lean)
-/
@[path]
private lemma e_zero_eq_one_eq
  [Field k] :
-- imply
  (e 0 : SweedlerH4 k) = 1 := by
-- proof
  apply SweedlerH4.e_zero_eq_one


-- created on 2026-10-23
