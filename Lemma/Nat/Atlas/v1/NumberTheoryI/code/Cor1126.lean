import Mathlib
import sympy.Basic
import Def.v1.Atlas.NumberTheoryI.code.Cor1126
open NumberField NumberField.InfinitePlace Module Fintype IsDedekindDomain


/--
[integralTensorToProduct_algebraMap_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1126.lean)
-/
@[path]
lemma integralTensorToProduct_algebraMap_comm
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {r : v.adicCompletionIntegers K} :
-- imply
  integralTensorToProduct (L := L) v (( letI := @Algebra.TensorProduct.rightAlgebra (𝓞 K) (𝓞 L) (v.adicCompletionIntegers K) _ _ _ _ _ algebraMap (v.adicCompletionIntegers K) (TensorProduct (𝓞 K) (𝓞 L) (v.adicCompletionIntegers K))) r) = ( letI : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }), Algebra (v.adicCompletionIntegers K) (w.val.adicCompletionIntegers L) := fun w => (completionEmbeddingIntegers v w.val w.prop).toAlgebra @algebraMap (v.adicCompletionIntegers K) ((ω : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) → ω.val.adicCompletionIntegers L) _ _ (Pi.algebra _ _)) r := by
-- proof
  funext w
  show (integralTensorToProduct (L := L) v
    (Algebra.TensorProduct.includeRight (R := 𝓞 K) r)) w =
    completionEmbeddingIntegers v w.val w.prop r
  have h1 : Algebra.TensorProduct.includeRight (R := 𝓞 K) r =
    (1 : 𝓞 L) ⊗ₜ[𝓞 K] r := Algebra.TensorProduct.includeRight_apply r
  rw [h1, integralTensorToProduct]
  simp only [Algebra.TensorProduct.productMap_apply_tmul, Pi.algHom_apply, map_one, one_mul]

/--
[algebraMap_valuation_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1126.lean)
-/
@[path]
private lemma algebraMap_valuation_le_one_eq
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {w : HeightOneSpectrum (𝓞 L)}
  {k : K}
-- given
  (hw : FinitePlace.LiesAbove w v)
  (hk : v.valuation K k ≤ 1) :
-- imply
  w.valuation L (algebraMap K L k) ≤ 1 := by
-- proof
  apply algebraMap_valuation_le_one v w hw k hk

/--
[completionEmbedding_finite_mem_integers](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1126.lean)
-/
@[path]
private lemma completionEmbedding_finite_mem_integers_eq
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {w : HeightOneSpectrum (𝓞 L)}
  {x : v.adicCompletionIntegers K}
-- given
  (hw : FinitePlace.LiesAbove w v) :
-- imply
  (completionEmbedding_finite v w hw) x.val ∈ w.adicCompletionIntegers L := by
-- proof
  apply completionEmbedding_finite_mem_integers v w hw x

/--
[completionEmbedding_finite_commutes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1126.lean)
-/
@[path]
private lemma completionEmbedding_finite_commutes_eq
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {w : HeightOneSpectrum (𝓞 L)}
  {r : 𝓞 K}
-- given
  (hw : FinitePlace.LiesAbove w v) :
-- imply
  (completionEmbedding_finite v w hw) ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) r).val) = ((algebraMap (𝓞 K) (w.adicCompletionIntegers L) r).val) := by
-- proof
  apply completionEmbedding_finite_commutes v w hw r


-- created on 2026-10-23
