import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.Polynomial.AdjoinRootTensorProduct
open scoped TensorProduct
open Ideal
open AdjoinRoot


/--
[quotientInfAlgEquivPiQuotient_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Polynomial/AdjoinRootTensorProduct.lean)
-/
@[path]
private lemma quotientInfAlgEquivPiQuotient_mk_eq
  [CommSemiring K] [CommRing R] [Algebra K R] [Finite ι]
  {I : ι → Ideal R}
  {r : R}
-- given
  (h : Pairwise fun i j => IsCoprime (I i) (I j)) :
-- imply
  quotientInfAlgEquivPiQuotient K R ι I h (Ideal.Quotient.mk _ r) =
    fun i ↦ Ideal.Quotient.mk (I i) r := by
-- proof
  apply Ideal.quotientInfAlgEquivPiQuotient_mk K R ι I h r

/--
[prodAlgEquiv_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Polynomial/AdjoinRootTensorProduct.lean)
-/
@[path]
private lemma prodAlgEquiv_mk_eq
  [Field K] [Fintype ι]
  {g : ι → Polynomial K}
  {p : Polynomial K}
-- given
  (hcop : Pairwise (fun i j => IsCoprime (g i) (g j))) :
-- imply
  prodAlgEquiv g hcop (AdjoinRoot.mk _ p) = fun i ↦ AdjoinRoot.mk (g i) p := by
-- proof
  apply AdjoinRoot.prodAlgEquiv_mk g hcop p

/--
[prodAlgEquiv_root](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Polynomial/AdjoinRootTensorProduct.lean)
-/
@[path]
private lemma prodAlgEquiv_root_eq
  [Field K] [Fintype ι]
  {g : ι → Polynomial K}
-- given
  (hcop : Pairwise (fun i j => IsCoprime (g i) (g j))) :
-- imply
  prodAlgEquiv g hcop (AdjoinRoot.root _) = fun i ↦ AdjoinRoot.root (g i) := by
-- proof
  apply AdjoinRoot.prodAlgEquiv_root g hcop

/--
[tensorProductAlgEquiv_mk_tmul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Polynomial/AdjoinRootTensorProduct.lean)
-/
@[path]
private lemma tensorProductAlgEquiv_mk_tmul_eq
  [Field K] [Field K'] [Algebra K K']
  {f p : Polynomial K}
  {c : K'} :
-- imply
  letI := by
-- proof
  apply AdjoinRoot.tensorProductAlgEquiv_mk_tmul f p c

/--
[tensorProductAlgEquiv_root_tmul_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Polynomial/AdjoinRootTensorProduct.lean)
-/
@[path]
private lemma tensorProductAlgEquiv_root_tmul_one_eq
  [Field K] [Field K'] [Algebra K K']
  {f : Polynomial K} :
-- imply
  letI := by
-- proof
  apply AdjoinRoot.tensorProductAlgEquiv_root_tmul_one f

/--
[tensorProductAlgEquivPi_mk_tmul_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Polynomial/AdjoinRootTensorProduct.lean)
-/
@[path]
private lemma tensorProductAlgEquivPi_mk_tmul_apply_eq
  [Field K] [Field K'] [Algebra K K'] [Fintype ι]
  {f p : Polynomial K}
  {g : ι → Polynomial K'}
  {c : K'}
  {i : ι}
-- given
  (hirr : ∀ i, Irreducible (g i))
  (hne : Pairwise fun i j => ¬Associated (g i) (g j))
  (hprod : Associated (Polynomial.map (algebraMap K K') f) (∏ i, g i)) :
-- imply
  letI := by
-- proof
  apply AdjoinRoot.tensorProductAlgEquivPi_mk_tmul_apply f p g hirr hne hprod c i

/--
[tensorProductAlgEquivPi_root_tmul_one_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Polynomial/AdjoinRootTensorProduct.lean)
-/
@[path]
private lemma tensorProductAlgEquivPi_root_tmul_one_apply_eq
  [Field K] [Field K'] [Algebra K K'] [Fintype ι]
  {f : Polynomial K}
  {g : ι → Polynomial K'}
  {i : ι}
-- given
  (hirr : ∀ i, Irreducible (g i))
  (hne : Pairwise fun i j => ¬Associated (g i) (g j))
  (hprod : Associated (Polynomial.map (algebraMap K K') f) (∏ i, g i)) :
-- imply
  letI := by
-- proof
  apply AdjoinRoot.tensorProductAlgEquivPi_root_tmul_one_apply f g hirr hne hprod i


-- created on 2026-10-20
