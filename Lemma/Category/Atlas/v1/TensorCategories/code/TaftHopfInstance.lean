import Mathlib
import sympy.Basic
import Instance.v1.Atlas.TensorCategories.code.TaftHopfInstance.Part3
open Coalgebra HopfAlgebra TaftAlgebraType


/--
[taft_all_axioms](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftHopfInstance.lean)
-/
@[path]
private lemma taft_all_axioms_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  [Fact (q ^ n = 1)]
  [TaftHopfData k n q]
  [TaftHopfData k n q] :
-- imply
  let g := gen_g (k := k) (q := q) (hn2' k n q) let x := gen_x (k := k) (q := q) (hn2' k n q) ((TensorProduct.assoc k A A A).toLinearMap ∘ₗ (taftComulLM k n q).rTensor A ∘ₗ taftComulLM k n q = (taftComulLM k n q).lTensor A ∘ₗ taftComulLM k n q) ∧ ((taftCounitLM k n q).rTensor A ∘ₗ taftComulLM k n q = TensorProduct.mk k k A 1) ∧ ((taftCounitLM k n q).lTensor A ∘ₗ taftComulLM k n q = (TensorProduct.mk k A k).flip 1) ∧ (taftComulLM k n q (1 : A) = 1) ∧ (∀ a b, taftComulLM k n q (a * b) = taftComulLM k n q a * taftComulLM k n q b) ∧ (taftCounitLM k n q (1 : A) = 1) ∧ (∀ a b, taftCounitLM k n q (a * b) = taftCounitLM k n q a * taftCounitLM k n q b) ∧ (LinearMap.mul' k A ∘ₗ (taftAntipodeLM k n q).rTensor A ∘ₗ taftComulLM k n q = Algebra.linearMap k A ∘ₗ taftCounitLM k n q) ∧ (LinearMap.mul' k A ∘ₗ (taftAntipodeLM k n q).lTensor A ∘ₗ taftComulLM k n q = Algebra.linearMap k A ∘ₗ taftCounitLM k n q) ∧ (taftComulLM k n q g = g ⊗ₜ[k] g) ∧ (taftComulLM k n q x = x ⊗ₜ[k] g + 1 ⊗ₜ[k] x) ∧ (taftCounitLM k n q g = (1 : k)) ∧ (taftCounitLM k n q x = (0 : k)) ∧ (taftAntipodeLM k n q g = g ^ (n - 1)) ∧ (taftAntipodeLM k n q x = -(g ^ (n - 1) * x)) := by
-- proof
  apply TaftAlgebraType.taft_all_axioms k n q

/--
[taft_coassoc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftHopfInstance.lean)
-/
@[path]
private lemma taft_coassoc_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  [Fact (q ^ n = 1)]
  [TaftHopfData k n q]
  [TaftHopfData k n q] :
-- imply
  (TensorProduct.assoc k A A A).toLinearMap ∘ₗ (taftComulLM k n q).rTensor A ∘ₗ taftComulLM k n q = (taftComulLM k n q).lTensor A ∘ₗ taftComulLM k n q := by
-- proof
  apply TaftAlgebraType.taft_coassoc k n q

/--
[taft_rTensor_counit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftHopfInstance.lean)
-/
@[path]
private lemma taft_rTensor_counit_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  [Fact (q ^ n = 1)]
  [TaftHopfData k n q]
  [TaftHopfData k n q] :
-- imply
  (taftCounitLM k n q).rTensor A ∘ₗ taftComulLM k n q = TensorProduct.mk k k A 1 := by
-- proof
  apply TaftAlgebraType.taft_rTensor_counit k n q

/--
[taft_lTensor_counit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftHopfInstance.lean)
-/
@[path]
private lemma taft_lTensor_counit_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  [Fact (q ^ n = 1)]
  [TaftHopfData k n q]
  [TaftHopfData k n q] :
-- imply
  (taftCounitLM k n q).lTensor A ∘ₗ taftComulLM k n q = (TensorProduct.mk k A k).flip 1 := by
-- proof
  apply TaftAlgebraType.taft_lTensor_counit k n q

/--
[taft_comul_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftHopfInstance.lean)
-/
@[path]
private lemma taft_comul_one_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  [Fact (q ^ n = 1)]
  [TaftHopfData k n q]
  [TaftHopfData k n q] :
-- imply
  taftComulLM k n q (1 : A) = 1 := by
-- proof
  apply TaftAlgebraType.taft_comul_one k n q

/--
[taft_comul_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftHopfInstance.lean)
-/
@[path]
private lemma taft_comul_mul_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  [Fact (q ^ n = 1)]
  [TaftHopfData k n q]
  [TaftHopfData k n q]
  {a b : A} :
-- imply
  taftComulLM k n q (a * b) = taftComulLM k n q a * taftComulLM k n q b := by
-- proof
  apply TaftAlgebraType.taft_comul_mul k n q a b

/--
[taft_counit_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftHopfInstance.lean)
-/
@[path]
private lemma taft_counit_one_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  [Fact (q ^ n = 1)]
  [TaftHopfData k n q]
  [TaftHopfData k n q] :
-- imply
  taftCounitLM k n q (1 : A) = 1 := by
-- proof
  apply TaftAlgebraType.taft_counit_one k n q

/--
[taft_counit_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftHopfInstance.lean)
-/
@[path]
private lemma taft_counit_mul_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  [Fact (q ^ n = 1)]
  [TaftHopfData k n q]
  [TaftHopfData k n q]
  {a b : A} :
-- imply
  taftCounitLM k n q (a * b) = taftCounitLM k n q a * taftCounitLM k n q b := by
-- proof
  apply TaftAlgebraType.taft_counit_mul k n q a b

/--
[taft_hopf_rTensor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftHopfInstance.lean)
-/
@[path]
private lemma taft_hopf_rTensor_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  [Fact (q ^ n = 1)]
  [TaftHopfData k n q]
  [TaftHopfData k n q] :
-- imply
  LinearMap.mul' k A ∘ₗ (taftAntipodeLM k n q).rTensor A ∘ₗ taftComulLM k n q = Algebra.linearMap k A ∘ₗ taftCounitLM k n q := by
-- proof
  apply TaftAlgebraType.taft_hopf_rTensor k n q

/--
[taft_hopf_lTensor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftHopfInstance.lean)
-/
@[path]
private lemma taft_hopf_lTensor_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  [Fact (q ^ n = 1)]
  [TaftHopfData k n q]
  [TaftHopfData k n q] :
-- imply
  LinearMap.mul' k A ∘ₗ (taftAntipodeLM k n q).lTensor A ∘ₗ taftComulLM k n q = Algebra.linearMap k A ∘ₗ taftCounitLM k n q := by
-- proof
  apply TaftAlgebraType.taft_hopf_lTensor k n q

/--
[taft_comul_gen_g](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftHopfInstance.lean)
-/
@[path]
private lemma taft_comul_gen_g_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  [Fact (q ^ n = 1)]
  [TaftHopfData k n q]
  [TaftHopfData k n q] :
-- imply
  taftComulLM k n q (gen_g (k := k) (q := q) (hn2' k n q)) = gen_g (hn2' k n q) ⊗ₜ[k] gen_g (hn2' k n q) := by
-- proof
  apply TaftAlgebraType.taft_comul_gen_g k n q

/--
[taft_comul_gen_x](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftHopfInstance.lean)
-/
@[path]
private lemma taft_comul_gen_x_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  [Fact (q ^ n = 1)]
  [TaftHopfData k n q]
  [TaftHopfData k n q] :
-- imply
  taftComulLM k n q (gen_x (k := k) (q := q) (hn2' k n q)) = gen_x (hn2' k n q) ⊗ₜ[k] gen_g (hn2' k n q) + 1 ⊗ₜ[k] gen_x (hn2' k n q) := by
-- proof
  apply TaftAlgebraType.taft_comul_gen_x k n q

/--
[taft_counit_gen_g](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftHopfInstance.lean)
-/
@[path]
private lemma taft_counit_gen_g_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  [Fact (q ^ n = 1)]
  [TaftHopfData k n q]
  [TaftHopfData k n q] :
-- imply
  taftCounitLM k n q (gen_g (k := k) (q := q) (hn2' k n q)) = (1 : k) := by
-- proof
  apply TaftAlgebraType.taft_counit_gen_g k n q

/--
[taft_counit_gen_x](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftHopfInstance.lean)
-/
@[path]
private lemma taft_counit_gen_x_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  [Fact (q ^ n = 1)]
  [TaftHopfData k n q]
  [TaftHopfData k n q] :
-- imply
  taftCounitLM k n q (gen_x (k := k) (q := q) (hn2' k n q)) = (0 : k) := by
-- proof
  apply TaftAlgebraType.taft_counit_gen_x k n q

/--
[taft_antipode_gen_g](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftHopfInstance.lean)
-/
@[path]
private lemma taft_antipode_gen_g_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  [Fact (q ^ n = 1)]
  [TaftHopfData k n q]
  [TaftHopfData k n q] :
-- imply
  taftAntipodeLM k n q (gen_g (k := k) (q := q) (hn2' k n q)) = gen_g (hn2' k n q) ^ (n - 1) := by
-- proof
  apply TaftAlgebraType.taft_antipode_gen_g k n q

/--
[taft_antipode_gen_x](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftHopfInstance.lean)
-/
@[path]
private lemma taft_antipode_gen_x_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  [Fact (q ^ n = 1)]
  [TaftHopfData k n q]
  [TaftHopfData k n q] :
-- imply
  taftAntipodeLM k n q (gen_x (k := k) (q := q) (hn2' k n q)) = -(gen_g (hn2' k n q) ^ (n - 1) * gen_x (hn2' k n q)) := by
-- proof
  apply TaftAlgebraType.taft_antipode_gen_x k n q

/--
[taft_comul_is](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftHopfInstance.lean)
-/
@[path]
private lemma taft_comul_is_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  [Fact (q ^ n = 1)]
  [TaftHopfData k n q]
  [TaftHopfData k n q] :
-- imply
  (CoalgebraStruct.comul : A →ₗ[k] _) = taftComulLM k n q := by
-- proof
  apply TaftAlgebraType.taft_comul_is k n q

/--
[taft_counit_is](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftHopfInstance.lean)
-/
@[path]
private lemma taft_counit_is_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  [Fact (q ^ n = 1)]
  [TaftHopfData k n q]
  [TaftHopfData k n q] :
-- imply
  (CoalgebraStruct.counit : A →ₗ[k] k) = taftCounitLM k n q := by
-- proof
  apply TaftAlgebraType.taft_counit_is k n q

/--
[taft_antipode_is](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftHopfInstance.lean)
-/
@[path]
private lemma taft_antipode_is_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  [Fact (q ^ n = 1)]
  [TaftHopfData k n q]
  [TaftHopfData k n q] :
-- imply
  (HopfAlgebraStruct.antipode (R := k) : A →ₗ[k] _) = taftAntipodeLM k n q := by
-- proof
  apply TaftAlgebraType.taft_antipode_is k n q


-- created on 2026-10-23
