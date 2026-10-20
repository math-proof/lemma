import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.KernelsLemma
open Polynomial
open scoped BigOperators
open MathlibExt.LinearAlgebra.KernelsLemmaWanted


/--
[iSup_ker_aeval_eq_ker_aeval_prod_of_pairwise_isCoprime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/KernelsLemma.lean)
-/
@[path]
private lemma iSup_ker_aeval_eq_ker_aeval_prod_of_pairwise_isCoprime_eq
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
  apply MathlibExt.LinearAlgebra.KernelsLemmaWanted.iSup_ker_aeval_eq_ker_aeval_prod_of_pairwise_isCoprime f p hcop s

/--
[supIndep_ker_aeval_of_pairwise_isCoprime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/KernelsLemma.lean)
-/
@[path]
private lemma supIndep_ker_aeval_of_pairwise_isCoprime_eq
  [CommRing R] [AddCommGroup M] [Module R M]
  {f : Module.End R M}
  {p : ι → R[X]}
  {s : Finset ι}
-- given
  (hcop : Pairwise fun i j => IsCoprime (p i) (p j)) :
-- imply
  s.SupIndep fun i => LinearMap.ker (aeval f (p i)) := by
-- proof
  apply MathlibExt.LinearAlgebra.KernelsLemmaWanted.supIndep_ker_aeval_of_pairwise_isCoprime f p hcop s

/--
[iSupIndep_ker_aeval_and_iSup_eq_of_pairwise_isCoprime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/KernelsLemma.lean)
-/
@[path]
private lemma iSupIndep_ker_aeval_and_iSup_eq_of_pairwise_isCoprime_eq
  [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
  {f : Module.End R M}
  {p : ι → R[X]}
-- given
  (hcop : Pairwise fun i j => IsCoprime (p i) (p j)) :
-- imply
  iSupIndep (fun i => LinearMap.ker (aeval f (p i))) ∧
    (⨆ i, LinearMap.ker (aeval f (p i))) = LinearMap.ker (aeval f (∏ i, p i)) := by
-- proof
  apply MathlibExt.LinearAlgebra.KernelsLemmaWanted.iSupIndep_ker_aeval_and_iSup_eq_of_pairwise_isCoprime f p hcop

/--
[kernels_lemma_pairwise_isCoprime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/KernelsLemma.lean)
-/
@[path]
private lemma kernels_lemma_pairwise_isCoprime_eq
  [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
  {f : Module.End R M}
  {p : ι → R[X]}
-- given
  (hcop : Pairwise fun i j => IsCoprime (p i) (p j)) :
-- imply
  iSupIndep (fun i => LinearMap.ker (aeval f (p i))) ∧
    (⨆ i, LinearMap.ker (aeval f (p i))) = LinearMap.ker (aeval f (∏ i, p i)) := by
-- proof
  apply MathlibExt.LinearAlgebra.KernelsLemmaWanted.kernels_lemma_pairwise_isCoprime f p hcop


-- created on 2026-10-20
