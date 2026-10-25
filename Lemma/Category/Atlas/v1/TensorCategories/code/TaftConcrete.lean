import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.TensorCategories.code.TaftConcrete.Part4
open TaftAlgebraType


namespace TaftAlgebraType

/--
[e_zero_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftConcrete.lean)
-/
@[path]
lemma e_zero_eq_one
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  [Fact (q ^ n = 1)] :
-- imply
  (e zp : TaftAlgebraType n q k) = 1 := by
-- proof
  ext m; simp only [coeff_e, coeff_one, eq_comm]

end TaftAlgebraType

/--
[coeff_zero'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftConcrete.lean)
-/
@[path]
private lemma coeff_zero'_eq
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  {i : Fin n × Fin n} :
-- imply
  (0 : TaftAlgebraType n q k).coeff i = 0 := by
-- proof
  apply TaftAlgebraType.coeff_zero' i

/--
[coeff_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftConcrete.lean)
-/
@[path]
private lemma coeff_add_eq
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  {a b : TaftAlgebraType n q k}
  {i : Fin n × Fin n} :
-- imply
  (a + b).coeff i = a.coeff i + b.coeff i := by
-- proof
  apply TaftAlgebraType.coeff_add a b i

/--
[coeff_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftConcrete.lean)
-/
@[path]
private lemma coeff_neg_eq
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  {a : TaftAlgebraType n q k}
  {i : Fin n × Fin n} :
-- imply
  (-a).coeff i = -a.coeff i := by
-- proof
  apply TaftAlgebraType.coeff_neg a i

/--
[coeff_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftConcrete.lean)
-/
@[path]
private lemma coeff_sub_eq
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  {a b : TaftAlgebraType n q k}
  {i : Fin n × Fin n} :
-- imply
  (a - b).coeff i = a.coeff i - b.coeff i := by
-- proof
  apply TaftAlgebraType.coeff_sub a b i

/--
[coeff_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftConcrete.lean)
-/
@[path]
private lemma coeff_smul_eq
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  {r : k}
  {a : TaftAlgebraType n q k}
  {i : Fin n × Fin n} :
-- imply
  (r • a).coeff i = r * a.coeff i := by
-- proof
  apply TaftAlgebraType.coeff_smul r a i

/--
[coeff_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftConcrete.lean)
-/
@[path]
private lemma coeff_mul_eq
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  {a b : TaftAlgebraType n q k}
  {m : Fin n × Fin n} :
-- imply
  (a * b).coeff m = ∑ ij : Fin n × Fin n, ∑ cd : Fin n × Fin n, a.coeff ij * b.coeff cd * basisMul q ij cd m := by
-- proof
  apply TaftAlgebraType.coeff_mul a b m

/--
[coeff_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftConcrete.lean)
-/
@[path]
private lemma coeff_one_eq
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  {m : Fin n × Fin n} :
-- imply
  (1 : TaftAlgebraType n q k).coeff m = if m = zp then 1 else 0 := by
-- proof
  apply TaftAlgebraType.coeff_one m

/--
[coeff_natCast](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftConcrete.lean)
-/
@[path]
private lemma coeff_natCast_eq
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  {c : ℕ}
  {m : Fin n × Fin n} :
-- imply
  (c : TaftAlgebraType n q k).coeff m = if m = zp then (c : k) else 0 := by
-- proof
  apply TaftAlgebraType.coeff_natCast c m

/--
[coeff_intCast](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftConcrete.lean)
-/
@[path]
private lemma coeff_intCast_eq
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  {c : ℤ}
  {m : Fin n × Fin n} :
-- imply
  (c : TaftAlgebraType n q k).coeff m = if m = zp then (c : k) else 0 := by
-- proof
  apply TaftAlgebraType.coeff_intCast c m

/--
[basisMul_ne_zero_imp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftConcrete.lean)
-/
@[path]
private lemma basisMul_ne_zero_imp_eq
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  {q : k}
  {ij cd ef : Fin n × Fin n}
-- given
  (h : basisMul q ij cd ef ≠ 0) :
-- imply
  ij.2.val + cd.2.val < n ∧ ef.1.val = (ij.1.val + cd.1.val) % n ∧ ef.2.val = ij.2.val + cd.2.val := by
-- proof
  apply TaftAlgebraType.basisMul_ne_zero_imp h

/--
[basisMul_zero_of_ge](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftConcrete.lean)
-/
@[path]
private lemma basisMul_zero_of_ge_eq
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  {q : k}
  {ij cd b : Fin n × Fin n}
-- given
  (h : ¬(ij.2.val + cd.2.val < n)) :
-- imply
  basisMul q ij cd b = 0 := by
-- proof
  apply TaftAlgebraType.basisMul_zero_of_ge q ij cd b h

/--
[basisMul_prod_zero_of_ge](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftConcrete.lean)
-/
@[path]
private lemma basisMul_prod_zero_of_ge_eq
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  {q : k}
  {ij cd p l m : Fin n × Fin n}
-- given
  (h : ¬(ij.2.val + cd.2.val + l.2.val < n)) :
-- imply
  basisMul q ij cd p * basisMul q p l m = 0 := by
-- proof
  apply TaftAlgebraType.basisMul_prod_zero_of_ge q ij cd p l m h

/--
[q_pow_nsq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftConcrete.lean)
-/
@[path]
private lemma q_pow_nsq_eq
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
-- given
  (hq : q ^ n = 1) :
-- imply
  q ^ (n * n) = 1 := by
-- proof
  apply TaftAlgebraType.q_pow_nsq hq

/--
[basisMul_id_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftConcrete.lean)
-/
@[path]
private lemma basisMul_id_left_eq
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  {cd ef : Fin n × Fin n}
-- given
  (hq : q ^ n = 1) :
-- imply
  basisMul q zp cd ef = if cd = ef then 1 else 0 := by
-- proof
  apply TaftAlgebraType.basisMul_id_left hq cd ef

/--
[basisMul_id_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftConcrete.lean)
-/
@[path]
private lemma basisMul_id_right_eq
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  {ij ef : Fin n × Fin n}
-- given
  (hq : q ^ n = 1) :
-- imply
  basisMul q ij zp ef = if ij = ef then 1 else 0 := by
-- proof
  apply TaftAlgebraType.basisMul_id_right hq ij ef

/--
[pow_nn_sub_eq_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftConcrete.lean)
-/
@[path]
private lemma pow_nn_sub_eq_inv_eq
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  {x : ℕ}
-- given
  (hq : q ^ n = 1)
  (hx : x ≤ n * n) :
-- imply
  q ^ (n * n - x) = (q ^ x)⁻¹ := by
-- proof
  apply TaftAlgebraType.pow_nn_sub_eq_inv hq x hx

/--
[pow_mul_mod_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftConcrete.lean)
-/
@[path]
private lemma pow_mul_mod_eq_eq
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  {b m : ℕ}
-- given
  (hq : q ^ n = 1) :
-- imply
  q ^ (b * m) = q ^ (b * (m % n)) := by
-- proof
  apply TaftAlgebraType.pow_mul_mod_eq hq b m

/--
[q_pow_assoc_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftConcrete.lean)
-/
@[path]
private lemma q_pow_assoc_identity_eq
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  {b c d e : ℕ}
-- given
  (hq : q ^ n = 1)
  (hb : b < n)
  (hc : c < n)
  (he : e < n)
  (hbd : b + d < n) :
-- imply
  q ^ (n * n - b * c) * q ^ (n * n - (b + d) * e) = q ^ (n * n - d * e) * q ^ (n * n - b * ((c + e) % n)) := by
-- proof
  apply TaftAlgebraType.q_pow_assoc_identity hq b c d e hb hc he hbd

/--
[hq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftConcrete.lean)
-/
@[path]
private lemma hq_eq
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  [Fact (q ^ n = 1)] :
-- imply
  q ^ n = 1 := by
-- proof
  apply TaftAlgebraType.hq

/--
[mod_add_mod](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftConcrete.lean)
-/
@[path]
private lemma mod_add_mod_eq
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  [Fact (q ^ n = 1)]
  {a b c : ℕ}
-- given
  (_hn : 0 < n) :
-- imply
  ((a + b) % n + c) % n = (a + (b + c) % n) % n := by
-- proof
  apply TaftAlgebraType.mod_add_mod a b c _hn

/--
[basisMul_assoc_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftConcrete.lean)
-/
@[path]
private lemma basisMul_assoc_eq_eq
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  [Fact (q ^ n = 1)]
  {ij cd l m : Fin n × Fin n} :
-- imply
  ∑ p : Fin n × Fin n, basisMul q ij cd p * basisMul q p l m = ∑ r : Fin n × Fin n, basisMul q cd l r * basisMul q ij r m := by
-- proof
  apply TaftAlgebraType.basisMul_assoc_eq ij cd l m

/--
[finrank_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftConcrete.lean)
-/
@[path]
private lemma finrank_eq_eq
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  [Fact (q ^ n = 1)] :
-- imply
  Module.finrank k (TaftAlgebraType n q k) = n * n := by
-- proof
  apply TaftAlgebraType.finrank_eq

/--
[coeff_e](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftConcrete.lean)
-/
@[path]
private lemma coeff_e_eq
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  [Fact (q ^ n = 1)]
  {ij p : Fin n × Fin n} :
-- imply
  (e ij : TaftAlgebraType n q k).coeff p = if ij = p then 1 else 0 := by
-- proof
  apply TaftAlgebraType.coeff_e ij p


-- created on 2026-10-23
