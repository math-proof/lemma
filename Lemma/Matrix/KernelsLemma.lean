import Mathlib
import sympy.Basic
open Polynomial
open scoped BigOperators


namespace MathlibExt.LinearAlgebra.KernelsLemmaWanted

/--
[iSup_ker_aeval_eq_ker_aeval_prod_of_pairwise_isCoprime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/KernelsLemma.lean)
-/
@[path]
lemma iSup_ker_aeval_eq_ker_aeval_prod_of_pairwise_isCoprime
  [CommRing R] [AddCommGroup M] [Module R M]
  {f : Module.End R M}
  {p : ι → R[X]}
  {s : Finset ι}
-- given
  (hcop : Pairwise fun i j => IsCoprime (p i) (p j)) :
-- imply
  (⨆ i ∈ s, LinearMap.ker (aeval f (p i))) =
    LinearMap.ker (aeval f (∏ i ∈ s, p i)) := by
-- proof
  classical
  induction s using Finset.induction_on with
  | empty =>
    ext x
    simp [LinearMap.mem_ker]
  | @insert a s ha ih =>
    have hcop_prod : IsCoprime (p a) (∏ i ∈ s, p i) := by
      apply IsCoprime.prod_right
      intro i hi
      exact hcop (ne_of_mem_of_not_mem hi ha).symm
    rw [Finset.prod_insert ha, Finset.iSup_insert,
      ← Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime f hcop_prod, ← ih]

end MathlibExt.LinearAlgebra.KernelsLemmaWanted

namespace MathlibExt.LinearAlgebra.KernelsLemmaWanted

/--
[supIndep_ker_aeval_of_pairwise_isCoprime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/KernelsLemma.lean)
-/
@[path]
lemma supIndep_ker_aeval_of_pairwise_isCoprime
  [CommRing R] [AddCommGroup M] [Module R M]
  {f : Module.End R M}
  {p : ι → R[X]}
  {s : Finset ι}
-- given
  (hcop : Pairwise fun i j => IsCoprime (p i) (p j)) :
-- imply
  s.SupIndep fun i => LinearMap.ker (aeval f (p i)) := by
-- proof
  classical
  intro t _ i _ hit
  rw [Finset.sup_eq_iSup,
    iSup_ker_aeval_eq_ker_aeval_prod_of_pairwise_isCoprime f p hcop t]
  apply Polynomial.disjoint_ker_aeval_of_isCoprime f
  apply IsCoprime.prod_right
  intro j hj
  exact hcop (ne_of_mem_of_not_mem hj hit).symm

end MathlibExt.LinearAlgebra.KernelsLemmaWanted

namespace MathlibExt.LinearAlgebra.KernelsLemmaWanted

/--
[iSupIndep_ker_aeval_and_iSup_eq_of_pairwise_isCoprime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/KernelsLemma.lean)
-/
@[path]
lemma iSupIndep_ker_aeval_and_iSup_eq_of_pairwise_isCoprime
  [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
  {f : Module.End R M}
  {p : ι → R[X]}
-- given
  (hcop : Pairwise fun i j => IsCoprime (p i) (p j)) :
-- imply
  iSupIndep (fun i => LinearMap.ker (aeval f (p i))) ∧
    (⨆ i, LinearMap.ker (aeval f (p i))) = LinearMap.ker (aeval f (∏ i, p i)) := by
-- proof
  classical
  constructor
  · apply iSupIndep_iff_supIndep_univ.mpr
    exact supIndep_ker_aeval_of_pairwise_isCoprime f p hcop Finset.univ
  · simpa using
    iSup_ker_aeval_eq_ker_aeval_prod_of_pairwise_isCoprime f p hcop Finset.univ

end MathlibExt.LinearAlgebra.KernelsLemmaWanted

namespace MathlibExt.LinearAlgebra.KernelsLemmaWanted

/--
[kernels_lemma_pairwise_isCoprime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/KernelsLemma.lean)
-/
@[path]
lemma kernels_lemma_pairwise_isCoprime
  [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
  {f : Module.End R M}
  {p : ι → R[X]}
-- given
  (hcop : Pairwise fun i j => IsCoprime (p i) (p j)) :
-- imply
  iSupIndep (fun i => LinearMap.ker (aeval f (p i))) ∧
    (⨆ i, LinearMap.ker (aeval f (p i))) = LinearMap.ker (aeval f (∏ i, p i)) := by
-- proof
  exact iSupIndep_ker_aeval_and_iSup_eq_of_pairwise_isCoprime f p hcop

end MathlibExt.LinearAlgebra.KernelsLemmaWanted


-- created on 2026-10-20
-- updated on 2026-10-23
