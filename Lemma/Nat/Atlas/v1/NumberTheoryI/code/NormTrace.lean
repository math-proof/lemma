import Mathlib
import Initialize.Tactic.Attr.Basic
open Module Algebra Polynomial IntermediateField
open TensorProduct


/--
[norm_eq_det_leftMulMatrix](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/NormTrace.lean)
-/
@[path]
lemma norm_eq_det_leftMulMatrix
  [CommRing A]
  [CommRing B]
  [Algebra A B]
  [Fintype ι]
  [DecidableEq ι]
  {basis : Basis ι A B}
  {b : B} :
-- imply
  Algebra.norm A b = (Algebra.leftMulMatrix basis b).det :=
-- proof
  Algebra.norm_eq_matrix_det basis b

/--
[trace_eq_trace_leftMulMatrix](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/NormTrace.lean)
-/
@[path]
lemma trace_eq_trace_leftMulMatrix
  [CommRing A]
  [CommRing B]
  [Algebra A B]
  [Fintype ι]
  [DecidableEq ι]
  {basis : Basis ι A B}
  {b : B} :
-- imply
  Algebra.trace A B b = (Algebra.leftMulMatrix basis b).trace :=
-- proof
  Algebra.trace_eq_matrix_trace basis b
section NormTraceBaseChange
open TensorProduct
variable {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A']
variable {B : Type*} [CommRing B] [Algebra A B]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
[leftMulMatrix_baseChange](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/NormTrace.lean)
-/
@[path]
lemma leftMulMatrix_baseChange
  [CommRing A]
  [CommRing A']
  [Algebra A A']
  [CommRing B]
  [Algebra A B]
  [Fintype ι]
  [DecidableEq ι]
  {bB : Basis ι A B}
  {b : B} :
-- imply
  @Algebra.leftMulMatrix A' (A' ⊗[A] B) _ _ (Algebra.TensorProduct.leftAlgebra) ι _ _ (bB.baseChange A') (Algebra.TensorProduct.includeRight b) = (algebraMap A A').mapMatrix (Algebra.leftMulMatrix bB b) := by
-- proof
  ext i j
  simp only [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply, Basis.baseChange_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', TensorProduct.tmul_mul_tmul, mul_one,
    Basis.baseChange_repr_tmul, Algebra.algebraMap_eq_smul_one, mul_one]

/--
[norm_baseChange](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/NormTrace.lean)
-/
@[path]
lemma norm_baseChange
  [CommRing A]
  [CommRing A']
  [Algebra A A']
  [CommRing B]
  [Algebra A B]
  [Fintype ι]
  [DecidableEq ι]
  {bB : Basis ι A B}
  {b : B} :
-- imply
  algebraMap A A' (Algebra.norm A b) = @Algebra.norm A' (A' ⊗[A] B) _ _ (Algebra.TensorProduct.leftAlgebra) (Algebra.TensorProduct.includeRight b) := by
-- proof
  rw [Algebra.norm_eq_matrix_det bB,
    @Algebra.norm_eq_matrix_det A' (A' ⊗[A] B) _ _ (Algebra.TensorProduct.leftAlgebra) ι _ _
      (bB.baseChange A'),
    leftMulMatrix_baseChange bB b, RingHom.map_det]

/--
[trace_baseChange](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/NormTrace.lean)
-/
@[path]
lemma trace_baseChange
  [CommRing A]
  [CommRing A']
  [Algebra A A']
  [CommRing B]
  [Algebra A B]
  [Fintype ι]
  [DecidableEq ι]
  {bB : Basis ι A B}
  {b : B} :
-- imply
  algebraMap A A' (Algebra.trace A B b) = @Algebra.trace A' (A' ⊗[A] B) _ _ (Algebra.TensorProduct.leftAlgebra) (Algebra.TensorProduct.includeRight b) := by
-- proof
  rw [Algebra.trace_eq_matrix_trace bB,
    @Algebra.trace_eq_matrix_trace A' (A' ⊗[A] B) _ _ (Algebra.TensorProduct.leftAlgebra) ι _ _
      (bB.baseChange A'),
    leftMulMatrix_baseChange bB b]
  simp only [RingHom.mapMatrix_apply]
  exact AddMonoidHom.map_trace (algebraMap A A') _

/--
[free_norm_trace_baseChange](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/NormTrace.lean)
-/
@[path]
lemma free_norm_trace_baseChange
  [CommRing A]
  [CommRing A']
  [Algebra A A']
  [CommRing B]
  [Algebra A B]
  [Fintype ι]
  [DecidableEq ι]
  {bB : Basis ι A B} :
-- imply
  Nonempty (Basis ι A' (A' ⊗[A] B)) ∧ (∀ b : B, algebraMap A A' (Algebra.norm A b) = @Algebra.norm A' (A' ⊗[A] B) _ _ (Algebra.TensorProduct.leftAlgebra) (Algebra.TensorProduct.includeRight b)) ∧ (∀ b : B, algebraMap A A' (Algebra.trace A B b) = @Algebra.trace A' (A' ⊗[A] B) _ _ (Algebra.TensorProduct.leftAlgebra) (Algebra.TensorProduct.includeRight b)) :=
-- proof
  ⟨⟨bB.baseChange A'⟩, norm_baseChange bB, trace_baseChange bB⟩
end NormTraceBaseChange
section NormTraceEmbeddings
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (E : Type*) [Field E] [Algebra K E]

/--
[norm_eq_prod_embeddings'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/NormTrace.lean)
-/
@[path]
lemma norm_eq_prod_embeddings'
  [Field K]
  [Field L]
  [Algebra K L]
  {E : Type*}
  [Field E]
  [Algebra K E]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [IsAlgClosed E]
  {x : L} :
-- imply
  algebraMap K E (Algebra.norm K x) = ∏ σ : L →ₐ[K] E, σ x :=
-- proof
  Algebra.norm_eq_prod_embeddings K E x

/--
[trace_eq_sum_embeddings'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/NormTrace.lean)
-/
@[path]
lemma trace_eq_sum_embeddings'
  [Field K]
  [Field L]
  [Algebra K L]
  {E : Type*}
  [Field E]
  [Algebra K E]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [IsAlgClosed E]
  {x : L} :
-- imply
  algebraMap K E (Algebra.trace K L x) = ∑ σ : L →ₐ[K] E, σ x :=
-- proof
  trace_eq_sum_embeddings E
end NormTraceEmbeddings
noncomputable section

/--
[norm_eq_prod_roots_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/NormTrace.lean)
-/
@[path]
lemma norm_eq_prod_roots_pow
  [Field K]
  [Field L]
  [Algebra K L]
  {F : Type*}
  [Field F]
  [Algebra K F]
  {x : L}
-- given
  (hF : ((minpoly K x).map (algebraMap K F)).Splits) :
-- imply
  algebraMap K F (Algebra.norm K x) = ((minpoly K x).aroots F).prod ^ Module.finrank K⟮x⟯ L :=
-- proof
  Algebra.norm_eq_prod_roots F hF

/--
[trace_eq_smul_sum_roots](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/NormTrace.lean)
-/
@[path]
lemma trace_eq_smul_sum_roots
  [Field K]
  [Field L]
  [Algebra K L]
  [Field F]
  [Algebra K F]
  [FiniteDimensional K L]
  {x : L}
-- given
  (hF : ((minpoly K x).map (algebraMap K F)).Splits) :
-- imply
  algebraMap K F (Algebra.trace K L x) = Module.finrank K⟮x⟯ L • ((minpoly K x).aroots F).sum :=
-- proof
  trace_eq_sum_roots hF

/--
[norm_eq_neg_one_pow_mul_coeff_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/NormTrace.lean)
-/
@[path]
lemma norm_eq_neg_one_pow_mul_coeff_zero
  [Field K]
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  {x : L} :
-- imply
  Algebra.norm K x = (-1) ^ ((minpoly K x).natDegree * Module.finrank K⟮x⟯ L) * ((minpoly K x).coeff 0) ^ Module.finrank K⟮x⟯ L := by
-- proof
  have hx : IsIntegral K x := .of_finite K x
  rw [Algebra.norm_eq_norm_adjoin K x]
  have key := PowerBasis.norm_gen_eq_coeff_zero_minpoly (IntermediateField.adjoin.powerBasis hx)
  rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.adjoin.powerBasis_dim,
    IntermediateField.minpoly_gen] at key
  rw [key, mul_pow, ← pow_mul]

/--
[trace_eq_neg_finrank_mul_nextCoeff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/NormTrace.lean)
-/
@[path]
lemma trace_eq_neg_finrank_mul_nextCoeff
  [Field K]
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  {x : L} :
-- imply
  Algebra.trace K L x = -(↑(Module.finrank K⟮x⟯ L) : K) * (minpoly K x).nextCoeff := by
-- proof
  rw [trace_eq_finrank_mul_minpoly_nextCoeff]
  ring
section NormTraceIntegrality
variable {A : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]
variable [Algebra A L] [IsScalarTower A K L]

/--
[norm_mem_of_isIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/NormTrace.lean)
-/
@[path]
lemma norm_mem_of_isIntegral
  [CommRing A]
  [IsDomain A]
  [IsIntegrallyClosed A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra A L]
  [IsScalarTower A K L]
  {x : L}
-- given
  (hx : IsIntegral A x) :
-- imply
  ∃ a : A, algebraMap A K a = Algebra.norm K x :=
-- proof
  IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_norm K hx)

/--
[trace_mem_of_isIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/NormTrace.lean)
-/
@[path]
lemma trace_mem_of_isIntegral
  [CommRing A]
  [IsDomain A]
  [IsIntegrallyClosed A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra A L]
  [IsScalarTower A K L]
  {x : L}
-- given
  (hx : IsIntegral A x) :
-- imply
  ∃ a : A, algebraMap A K a = Algebra.trace K L x :=
-- proof
  IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_trace hx)
end NormTraceIntegrality
section NormTraceTransitivity

/--
[norm_tower](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/NormTrace.lean)
-/
@[path]
lemma norm_tower
  [CommRing A]
  [CommRing B]
  [Ring C]
  [Algebra A B]
  [Algebra A C]
  [Algebra B C]
  [IsScalarTower A B C]
  [Module.Free A B]
  [Module.Free B C]
  {x : C} :
-- imply
  Algebra.norm A (Algebra.norm B x) = Algebra.norm A x :=
-- proof
  Algebra.norm_norm

/--
[trace_tower](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/NormTrace.lean)
-/
@[path]
lemma trace_tower
  [CommRing A]
  [CommRing B]
  [CommRing C]
  [Algebra A B]
  [Algebra A C]
  [Algebra B C]
  [IsScalarTower A B C]
  [Module.Free A B]
  [Module.Finite A B]
  [Module.Free B C]
  [Module.Finite B C]
  {x : C} :
-- imply
  Algebra.trace A B (Algebra.trace B C x) = Algebra.trace A C x :=
-- proof
  Algebra.trace_trace x
end NormTraceTransitivity
end


-- created on 2026-10-23
