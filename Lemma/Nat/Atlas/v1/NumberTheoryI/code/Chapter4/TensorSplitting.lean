import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.NumberTheoryI.code.Chapter4.TensorSplitting.Part2
open Polynomial TensorProduct TensorSplitting


/--
[span_prod_eq_biInf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter4/TensorSplitting.lean)
-/
@[path]
private lemma span_prod_eq_biInf_eq
  [CommRing R]
  [DecidableEq ι]
  {s : Finset ι}
  {g : ι → R}
-- given
  (hc : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (g i) (g j)) :
-- imply
  Ideal.span ({∏ i ∈ s, g i} : Set R) = ⨅ i ∈ s, Ideal.span ({g i} : Set R) := by
-- proof
  apply TensorSplitting.span_prod_eq_biInf s g hc

/--
[span_prod_eq_iInf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter4/TensorSplitting.lean)
-/
@[path]
private lemma span_prod_eq_iInf_eq
  [CommRing R]
  [DecidableEq ι]
  [Fintype ι]
  {g : ι → R}
-- given
  (hc : Pairwise fun i j => IsCoprime (g i) (g j)) :
-- imply
  Ideal.span ({∏ i, g i} : Set R) = ⨅ i, Ideal.span ({g i} : Set R) := by
-- proof
  apply TensorSplitting.span_prod_eq_iInf g hc

/--
[isCoprime_of_irreducible_of_not_associated](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter4/TensorSplitting.lean)
-/
@[path]
private lemma isCoprime_of_irreducible_of_not_associated_eq
  [Field K]
  {p q : Polynomial K}
-- given
  (hp : Irreducible p)
  (hq : Irreducible q)
  (hne : ¬Associated p q) :
-- imply
  IsCoprime p q := by
-- proof
  apply TensorSplitting.isCoprime_of_irreducible_of_not_associated hp hq hne

/--
[quotientInfRingEquivPiQuotient_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter4/TensorSplitting.lean)
-/
@[path]
private lemma quotientInfRingEquivPiQuotient_algebraMap_eq
  [Field K']
  [DecidableEq ι]
  [Fintype ι]
  {I : ι → Ideal (Polynomial K')}
  {k : K'}
-- given
  (hc : Pairwise fun i j => IsCoprime (I i) (I j)) :
-- imply
  (Ideal.quotientInfRingEquivPiQuotient I hc) ((algebraMap K' _) k) = (algebraMap K' _) k := by
-- proof
  apply TensorSplitting.quotientInfRingEquivPiQuotient_algebraMap I hc k

/--
[polyEquivTensor'_symm_comp_includeRight](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter4/TensorSplitting.lean)
-/
@[path]
private lemma polyEquivTensor'_symm_comp_includeRight_eq
  [Field K]
  [Field K']
  [Algebra K K'] :
-- imply
  ((polyEquivTensor' K K').symm : K' ⊗[K] Polynomial K →+* Polynomial K').comp (↑(Algebra.TensorProduct.includeRight (R := K) (A := K') (B := Polynomial K)) : Polynomial K →+* K' ⊗[K] Polynomial K) = Polynomial.mapRingHom (algebraMap K K') := by
-- proof
  apply TensorSplitting.polyEquivTensor'_symm_comp_includeRight


-- created on 2026-10-23
