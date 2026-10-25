import Mathlib
import sympy.Basic
import Instance.v1.Atlas.TensorCategories.code.QuantumSl2Concrete.Part5
open Coalgebra HopfAlgebra SmallQuantumSl2 SmallQuantumSl2Alg
open scoped TensorProduct


namespace SmallQuantumSl2

/--
[coeff_finset_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Concrete.lean)
-/
@[path]
lemma coeff_finset_sum
  {n : ℕ}
  [Field k]
  {s : Finset (Fin n × Fin n × Fin n)}
  {f : Fin n × Fin n × Fin n → SmallQuantumSl2 n k}
  {j : Fin n × Fin n × Fin n} :
-- imply
  (∑ i ∈ s, f i).coeff j = ∑ i ∈ s, (f i).coeff j := by
-- proof
  induction s using Finset.cons_induction with
  | empty => simp [Finset.sum_empty]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, coeff_add, ih]

end SmallQuantumSl2

/--
[coeff_zero'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Concrete.lean)
-/
@[path]
private lemma coeff_zero'_eq
  {n : ℕ}
  [Field k]
  {i : Fin n × Fin n × Fin n} :
-- imply
  (0 : SmallQuantumSl2 n k).coeff i = 0 := by
-- proof
  apply SmallQuantumSl2.coeff_zero' i

/--
[coeff_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Concrete.lean)
-/
@[path]
private lemma coeff_add_eq
  {n : ℕ}
  [Field k]
  {a b : SmallQuantumSl2 n k}
  {i : Fin n × Fin n × Fin n} :
-- imply
  (a + b).coeff i = a.coeff i + b.coeff i := by
-- proof
  apply SmallQuantumSl2.coeff_add a b i

/--
[coeff_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Concrete.lean)
-/
@[path]
private lemma coeff_neg_eq
  {n : ℕ}
  [Field k]
  {a : SmallQuantumSl2 n k}
  {i : Fin n × Fin n × Fin n} :
-- imply
  (-a).coeff i = -a.coeff i := by
-- proof
  apply SmallQuantumSl2.coeff_neg a i

/--
[coeff_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Concrete.lean)
-/
@[path]
private lemma coeff_sub_eq
  {n : ℕ}
  [Field k]
  {a b : SmallQuantumSl2 n k}
  {i : Fin n × Fin n × Fin n} :
-- imply
  (a - b).coeff i = a.coeff i - b.coeff i := by
-- proof
  apply SmallQuantumSl2.coeff_sub a b i

/--
[coeff_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Concrete.lean)
-/
@[path]
private lemma coeff_smul_eq
  {n : ℕ}
  [Field k]
  {r : k}
  {a : SmallQuantumSl2 n k}
  {i : Fin n × Fin n × Fin n} :
-- imply
  (r • a).coeff i = r * a.coeff i := by
-- proof
  apply SmallQuantumSl2.coeff_smul r a i

/--
[coeff_basisVec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Concrete.lean)
-/
@[path]
private lemma coeff_basisVec_eq
  {n : ℕ}
  [Field k]
  {i j : Fin n × Fin n × Fin n} :
-- imply
  (basisVec i : SmallQuantumSl2 n k).coeff j = if i = j then 1 else 0 := by
-- proof
  apply SmallQuantumSl2.coeff_basisVec i j

/--
[K_pow_n_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Concrete.lean)
-/
@[path]
private lemma K_pow_n_eq_eq
  {n : ℕ}
  [Field k]
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k} :
-- imply
  (K n k q) ^ n = 1 := by
-- proof
  apply SmallQuantumSl2Alg.K_pow_n_eq n k q

/--
[E_pow_n_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Concrete.lean)
-/
@[path]
private lemma E_pow_n_eq_eq
  {n : ℕ}
  [Field k]
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k} :
-- imply
  (E n k q) ^ n = 0 := by
-- proof
  apply SmallQuantumSl2Alg.E_pow_n_eq n k q

/--
[F_pow_n_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Concrete.lean)
-/
@[path]
private lemma F_pow_n_eq_eq
  {n : ℕ}
  [Field k]
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k} :
-- imply
  (F n k q) ^ n = 0 := by
-- proof
  apply SmallQuantumSl2Alg.F_pow_n_eq n k q

/--
[K_mul_E_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Concrete.lean)
-/
@[path]
private lemma K_mul_E_eq_eq
  {n : ℕ}
  [Field k]
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k} :
-- imply
  K n k q * E n k q = q ^ 2 • (E n k q * K n k q) := by
-- proof
  apply SmallQuantumSl2Alg.K_mul_E_eq n k q

/--
[K_mul_F_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Concrete.lean)
-/
@[path]
private lemma K_mul_F_eq_eq
  {n : ℕ}
  [Field k]
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k} :
-- imply
  K n k q * F n k q = (q ^ 2)⁻¹ • (F n k q * K n k q) := by
-- proof
  apply SmallQuantumSl2Alg.K_mul_F_eq n k q

/--
[E_mul_F_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Concrete.lean)
-/
@[path]
private lemma E_mul_F_comm_eq
  {n : ℕ}
  [Field k]
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k} :
-- imply
  E n k q * F n k q - F n k q * E n k q = (q - q⁻¹)⁻¹ • (K n k q - K n k q ^ (n - 1)) := by
-- proof
  apply SmallQuantumSl2Alg.E_mul_F_comm n k q

/--
[K_mul_Kinv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Concrete.lean)
-/
@[path]
private lemma K_mul_Kinv_eq
  {n : ℕ}
  [Field k]
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
-- given
  (hn : 1 ≤ n) :
-- imply
  K n k q * Kinv n k q = 1 := by
-- proof
  apply SmallQuantumSl2Alg.K_mul_Kinv n k q hn

/--
[Kinv_mul_K](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Concrete.lean)
-/
@[path]
private lemma Kinv_mul_K_eq
  {n : ℕ}
  [Field k]
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
-- given
  (hn : 1 ≤ n) :
-- imply
  Kinv n k q * K n k q = 1 := by
-- proof
  apply SmallQuantumSl2Alg.Kinv_mul_K n k q hn

/--
[comul_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Concrete.lean)
-/
@[path]
private lemma comul_eq_eq
  {n : ℕ}
  [Field k]
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
  {n : ℕ}
  [Field k]
  {q : k}
  [hd : SmallQuantumSl2HopfData n k q]
  {x : SmallQuantumSl2Alg n k q} :
-- imply
  comul (R := k) x = hd.comulHom x := by
-- proof
  apply SmallQuantumSl2Alg.comul_eq n k q x

/--
[counit_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Concrete.lean)
-/
@[path]
private lemma counit_eq_eq
  {n : ℕ}
  [Field k]
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
  {n : ℕ}
  [Field k]
  {q : k}
  [hd : SmallQuantumSl2HopfData n k q]
  {x : SmallQuantumSl2Alg n k q} :
-- imply
  counit (R := k) x = hd.counitHom x := by
-- proof
  apply SmallQuantumSl2Alg.counit_eq n k q x

/--
[antipode_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Concrete.lean)
-/
@[path]
private lemma antipode_eq_eq
  {n : ℕ}
  [Field k]
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
  {n : ℕ}
  [Field k]
  {q : k}
  [hd : SmallQuantumSl2HopfData n k q]
  {x : SmallQuantumSl2Alg n k q} :
-- imply
  antipode k x = hd.antipodeLin x := by
-- proof
  apply SmallQuantumSl2Alg.antipode_eq n k q x


-- created on 2026-10-23
