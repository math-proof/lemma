import Mathlib
import sympy.Basic
import Instance.v1.Atlas.TensorCategories.code.QuantumSl2Instance
open Coalgebra HopfAlgebra SmallQuantumSl2Instance


/--
[q_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Instance.lean)
-/
@[path]
private lemma q_ne_zero_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
  [hyp : QuantumSl2Hypotheses n k q] :
-- imply
  q ≠ 0 := by
-- proof
  apply SmallQuantumSl2Instance.q_ne_zero n k q

/--
[q2_pow_n](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Instance.lean)
-/
@[path]
private lemma q2_pow_n_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
  [hyp : QuantumSl2Hypotheses n k q] :
-- imply
  (q ^ 2) ^ n = 1 := by
-- proof
  apply SmallQuantumSl2Instance.q2_pow_n n k q

/--
[one_lt_n](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Instance.lean)
-/
@[path]
private lemma one_lt_n_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
  [hyp : QuantumSl2Hypotheses n k q] :
-- imply
  1 < n := by
-- proof
  apply SmallQuantumSl2Instance.one_lt_n n k q

/--
[one_le_n](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Instance.lean)
-/
@[path]
private lemma one_le_n_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
  [hyp : QuantumSl2Hypotheses n k q] :
-- imply
  1 ≤ n := by
-- proof
  apply SmallQuantumSl2Instance.one_le_n n k q

/--
[n_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Instance.lean)
-/
@[path]
private lemma n_ne_zero_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
  [hyp : QuantumSl2Hypotheses n k q] :
-- imply
  n ≠ 0 := by
-- proof
  apply SmallQuantumSl2Instance.n_ne_zero n k q

/--
[DeltaK_pow_n](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Instance.lean)
-/
@[path]
private lemma DeltaK_pow_n_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
  [hyp : QuantumSl2Hypotheses n k q] :
-- imply
  DeltaK n k q ^ n = 1 := by
-- proof
  apply SmallQuantumSl2Instance.DeltaK_pow_n n k q

/--
[DeltaE_pow_n](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Instance.lean)
-/
@[path]
private lemma DeltaE_pow_n_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
  [hyp : QuantumSl2Hypotheses n k q] :
-- imply
  DeltaE n k q ^ n = 0 := by
-- proof
  apply SmallQuantumSl2Instance.DeltaE_pow_n n k q

/--
[K_pow_mul_F](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Instance.lean)
-/
@[path]
private lemma K_pow_mul_F_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
  [hyp : QuantumSl2Hypotheses n k q]
  {j : ℕ} :
-- imply
  KK ^ j * FF = ((q ^ 2)⁻¹) ^ j • (FF * KK ^ j) := by
-- proof
  apply SmallQuantumSl2Instance.K_pow_mul_F n k q j

/--
[inv_q2_pow_pred](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Instance.lean)
-/
@[path]
private lemma inv_q2_pow_pred_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
  [hyp : QuantumSl2Hypotheses n k q] :
-- imply
  ((q ^ 2)⁻¹) ^ (n - 1) = q ^ 2 := by
-- proof
  apply SmallQuantumSl2Instance.inv_q2_pow_pred n k q

/--
[Kinv_mul_F](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Instance.lean)
-/
@[path]
private lemma Kinv_mul_F_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
  [hyp : QuantumSl2Hypotheses n k q] :
-- imply
  Kinv * FF = (q ^ 2) • (FF * Kinv) := by
-- proof
  apply SmallQuantumSl2Instance.Kinv_mul_F n k q

/--
[DeltaF_pow_n](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Instance.lean)
-/
@[path]
private lemma DeltaF_pow_n_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
  [hyp : QuantumSl2Hypotheses n k q] :
-- imply
  DeltaF n k q ^ n = 0 := by
-- proof
  apply SmallQuantumSl2Instance.DeltaF_pow_n n k q

/--
[DeltaKE_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Instance.lean)
-/
@[path]
private lemma DeltaKE_comm_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
  [hyp : QuantumSl2Hypotheses n k q] :
-- imply
  DeltaK n k q * DeltaE n k q = q ^ 2 • (DeltaE n k q * DeltaK n k q) := by
-- proof
  apply SmallQuantumSl2Instance.DeltaKE_comm n k q

/--
[DeltaKF_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Instance.lean)
-/
@[path]
private lemma DeltaKF_comm_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
  [hyp : QuantumSl2Hypotheses n k q] :
-- imply
  DeltaK n k q * DeltaF n k q = (q ^ 2)⁻¹ • (DeltaF n k q * DeltaK n k q) := by
-- proof
  apply SmallQuantumSl2Instance.DeltaKF_comm n k q

/--
[K_pow_mul_E](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Instance.lean)
-/
@[path]
private lemma K_pow_mul_E_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
  [hyp : QuantumSl2Hypotheses n k q]
  {j : ℕ} :
-- imply
  KK ^ j * EE = (q ^ 2) ^ j • (EE * KK ^ j) := by
-- proof
  apply SmallQuantumSl2Instance.K_pow_mul_E n k q j

/--
[E_mul_K_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Instance.lean)
-/
@[path]
private lemma E_mul_K_pow_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
  [hyp : QuantumSl2Hypotheses n k q]
  {j : ℕ} :
-- imply
  EE * KK ^ j = ((q ^ 2)⁻¹) ^ j • (KK ^ j * EE) := by
-- proof
  apply SmallQuantumSl2Instance.E_mul_K_pow n k q j

/--
[E_mul_Kinv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Instance.lean)
-/
@[path]
private lemma E_mul_Kinv_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
  [hyp : QuantumSl2Hypotheses n k q] :
-- imply
  EE * Kinv = (q ^ 2) • (Kinv * EE) := by
-- proof
  apply SmallQuantumSl2Instance.E_mul_Kinv n k q

/--
[cross_term_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Instance.lean)
-/
@[path]
private lemma cross_term_eq_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
  [hyp : QuantumSl2Hypotheses n k q] :
-- imply
  (EE * Kinv) ⊗ₜ[k] (KK * FF) = (Kinv * EE) ⊗ₜ[k] (FF * KK) := by
-- proof
  apply SmallQuantumSl2Instance.cross_term_eq n k q

/--
[DeltaK_pow_pred](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Instance.lean)
-/
@[path]
private lemma DeltaK_pow_pred_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
  [hyp : QuantumSl2Hypotheses n k q] :
-- imply
  DeltaK n k q ^ (n - 1) = Kinv ⊗ₜ[k] Kinv := by
-- proof
  apply SmallQuantumSl2Instance.DeltaK_pow_pred n k q

/--
[DeltaEF_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Instance.lean)
-/
@[path]
private lemma DeltaEF_comm_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
  [hyp : QuantumSl2Hypotheses n k q] :
-- imply
  DeltaE n k q * DeltaF n k q - DeltaF n k q * DeltaE n k q = (q - q⁻¹)⁻¹ • (DeltaK n k q - DeltaK n k q ^ (n - 1)) := by
-- proof
  apply SmallQuantumSl2Instance.DeltaEF_comm n k q

/--
[antipodeLinAux_K](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Instance.lean)
-/
@[path]
private lemma antipodeLinAux_K_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
  [hyp : QuantumSl2Hypotheses n k q]
  [QuantumSl2StructuralAxioms n k q] :
-- imply
  antipodeLinAux n k q KK = Kinv := by
-- proof
  apply SmallQuantumSl2Instance.antipodeLinAux_K n k q

/--
[antipodeLinAux_E](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Instance.lean)
-/
@[path]
private lemma antipodeLinAux_E_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
  [hyp : QuantumSl2Hypotheses n k q]
  [QuantumSl2StructuralAxioms n k q] :
-- imply
  antipodeLinAux n k q EE = -(EE * Kinv) := by
-- proof
  apply SmallQuantumSl2Instance.antipodeLinAux_E n k q

/--
[antipodeLinAux_F](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Instance.lean)
-/
@[path]
private lemma antipodeLinAux_F_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
  [hyp : QuantumSl2Hypotheses n k q]
  [QuantumSl2StructuralAxioms n k q] :
-- imply
  antipodeLinAux n k q FF = -(KK * FF) := by
-- proof
  apply SmallQuantumSl2Instance.antipodeLinAux_F n k q

/--
[comulHomAux_K](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Instance.lean)
-/
@[path]
private lemma comulHomAux_K_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
  [hyp : QuantumSl2Hypotheses n k q]
  [QuantumSl2StructuralAxioms n k q] :
-- imply
  comulHomAux n k q KK = KK ⊗ₜ[k] KK := by
-- proof
  apply SmallQuantumSl2Instance.comulHomAux_K n k q

/--
[comulHomAux_E](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Instance.lean)
-/
@[path]
private lemma comulHomAux_E_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
  [hyp : QuantumSl2Hypotheses n k q]
  [QuantumSl2StructuralAxioms n k q] :
-- imply
  comulHomAux n k q EE = EE ⊗ₜ[k] KK + 1 ⊗ₜ[k] EE := by
-- proof
  apply SmallQuantumSl2Instance.comulHomAux_E n k q

/--
[comulHomAux_F](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Instance.lean)
-/
@[path]
private lemma comulHomAux_F_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
  [hyp : QuantumSl2Hypotheses n k q]
  [QuantumSl2StructuralAxioms n k q] :
-- imply
  comulHomAux n k q FF = FF ⊗ₜ[k] 1 + Kinv ⊗ₜ[k] FF := by
-- proof
  apply SmallQuantumSl2Instance.comulHomAux_F n k q

/--
[counitHomAux_K](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Instance.lean)
-/
@[path]
private lemma counitHomAux_K_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
  [hyp : QuantumSl2Hypotheses n k q]
  [QuantumSl2StructuralAxioms n k q] :
-- imply
  counitHomAux n k q KK = 1 := by
-- proof
  apply SmallQuantumSl2Instance.counitHomAux_K n k q

/--
[counitHomAux_E](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Instance.lean)
-/
@[path]
private lemma counitHomAux_E_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
  [hyp : QuantumSl2Hypotheses n k q]
  [QuantumSl2StructuralAxioms n k q] :
-- imply
  counitHomAux n k q EE = 0 := by
-- proof
  apply SmallQuantumSl2Instance.counitHomAux_E n k q

/--
[counitHomAux_F](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Instance.lean)
-/
@[path]
private lemma counitHomAux_F_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {q : k}
  [hyp : QuantumSl2Hypotheses n k q]
  [QuantumSl2StructuralAxioms n k q] :
-- imply
  counitHomAux n k q FF = 0 := by
-- proof
  apply SmallQuantumSl2Instance.counitHomAux_F n k q


-- created on 2026-10-23
