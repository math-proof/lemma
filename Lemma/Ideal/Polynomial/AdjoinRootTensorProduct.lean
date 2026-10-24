import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.Polynomial.AdjoinRootTensorProduct
open scoped TensorProduct
open Ideal
open AdjoinRoot


namespace Ideal

/--
[quotientInfAlgEquivPiQuotient_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Polynomial/AdjoinRootTensorProduct.lean)
-/
@[path]
lemma quotientInfAlgEquivPiQuotient_mk
  [CommSemiring K] [CommRing R] [Algebra K R] [Finite ι]
  {I : ι → Ideal R}
  {r : R}
-- given
  (h : Pairwise fun i j => IsCoprime (I i) (I j)) :
-- imply
  quotientInfAlgEquivPiQuotient K R ι I h (Ideal.Quotient.mk _ r) =
    fun i ↦ Ideal.Quotient.mk (I i) r :=
-- proof
  rfl
end Ideal


namespace AdjoinRoot

/--
[prodAlgEquiv_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Polynomial/AdjoinRootTensorProduct.lean)
-/
@[path]
lemma prodAlgEquiv_mk
  [Field K] [Fintype ι]
  {g : ι → Polynomial K}
  {p : Polynomial K}
-- given
  (hcop : Pairwise (fun i j => IsCoprime (g i) (g j))) :
-- imply
  prodAlgEquiv g hcop (AdjoinRoot.mk _ p) = fun i ↦ AdjoinRoot.mk (g i) p := by
-- proof
  classical
  rfl

end AdjoinRoot

namespace AdjoinRoot

/--
[prodAlgEquiv_root](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Polynomial/AdjoinRootTensorProduct.lean)
-/
@[path]
lemma prodAlgEquiv_root
  [Field K] [Fintype ι]
  {g : ι → Polynomial K}
-- given
  (hcop : Pairwise (fun i j => IsCoprime (g i) (g j))) :
-- imply
  prodAlgEquiv g hcop (AdjoinRoot.root _) = fun i ↦ AdjoinRoot.root (g i) := by
-- proof
  classical
  change prodAlgEquiv g hcop (AdjoinRoot.mk _ Polynomial.X) =
    fun i ↦ AdjoinRoot.mk (g i) Polynomial.X
  exact prodAlgEquiv_mk g hcop Polynomial.X

end AdjoinRoot

namespace AdjoinRoot

/--
[tensorProductAlgEquiv_mk_tmul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Polynomial/AdjoinRootTensorProduct.lean)
-/
@[path]
lemma tensorProductAlgEquiv_mk_tmul
  [Field K] [Field K'] [Algebra K K']
  {f p : Polynomial K}
  {c : K'} :
-- imply
  letI := by
-- proof
  rfl

end AdjoinRoot

namespace AdjoinRoot

/--
[tensorProductAlgEquiv_root_tmul_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Polynomial/AdjoinRootTensorProduct.lean)
-/
@[path]
lemma tensorProductAlgEquiv_root_tmul_one
  [Field K] [Field K'] [Algebra K K']
  {f : Polynomial K} :
-- imply
  letI := by
-- proof
  change tensorProductAlgEquiv f (AdjoinRoot.mk f Polynomial.X ⊗ₜ[K] (1 : K')) =
    AdjoinRoot.mk (Polynomial.map (algebraMap K K') f) Polynomial.X
  rw [tensorProductAlgEquiv_mk_tmul, one_smul, Polynomial.map_X]

end AdjoinRoot

namespace AdjoinRoot

/--
[tensorProductAlgEquivPi_mk_tmul_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Polynomial/AdjoinRootTensorProduct.lean)
-/
@[path]
lemma tensorProductAlgEquivPi_mk_tmul_apply
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
  classical
  rfl

end AdjoinRoot

namespace AdjoinRoot

/--
[tensorProductAlgEquivPi_root_tmul_one_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Polynomial/AdjoinRootTensorProduct.lean)
-/
@[path]
lemma tensorProductAlgEquivPi_root_tmul_one_apply
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
  change tensorProductAlgEquivPi f g hirr hne hprod
    (AdjoinRoot.mk f Polynomial.X ⊗ₜ[K] (1 : K')) i =
    AdjoinRoot.mk (g i) Polynomial.X
  rw [tensorProductAlgEquivPi_mk_tmul_apply, one_smul, Polynomial.map_X]

end AdjoinRoot


-- created on 2026-10-20
-- updated on 2026-10-23
