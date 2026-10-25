import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.RefinementCompatibility
open GLnBuilding


/--
[gapVector_mem_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/RefinementCompatibility.lean)
-/
@[path]
private lemma main
  [Field k]
  {n : ℕ}
  {σ : CompleteFlag k n}
  {j : Fin n}
  {i : Fin (n + 1)}
-- given
  (hσ : σ.IsStrictFlag)
  (hjlt : j.val < i.val) :
-- imply
  hσ.gapVector j ∈ σ.spaces i :=
-- proof
  hσ.gapVector_mem_of_le j i (by omega)



/--
[refinementFrame_sigma_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/RefinementCompatibility.lean)
-/
private lemma refinementFrame_sigma_eq
  [Field k]
  {n : ℕ}
  {σ : CompleteFlag k n}
  [FiniteDimensional k (Vec k n)]
  {i : Fin (n + 1)}
-- given
  (hσ : σ.IsStrictFlag) :
-- imply
  (⨆ j ∈ sigmaWitness i, (refinementFrame hσ).lines j) = σ.spaces i := by
-- proof
  have hFD : FiniteDimensional k ↥(σ.spaces i) :=
    FiniteDimensional.finiteDimensional_submodule (σ.spaces i)
  have hle : (⨆ j ∈ sigmaWitness i, (refinementFrame hσ).lines j) ≤ σ.spaces i := by
    apply iSup_le; intro j; apply iSup_le; intro hj
    simp only [sigmaWitness, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    show k ∙ hσ.gapVector j ≤ σ.spaces i
    rw [Submodule.span_singleton_le_iff_mem]
    exact gapVector_mem_of_lt hσ j i hj
  have hfr : Module.finrank k ↥(σ.spaces i) = (sigmaWitness i).card := by
    rw [hσ i, card_sigmaWitness_eq]
  exact biSup_span_singleton_eq_of_le_of_finrank
    hσ.linearIndependent_gapVectors (sigmaWitness i) (σ.spaces i) hle hfr


/--
[card_sigmaWitness_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/RefinementCompatibility.lean)
-/
private lemma card_sigmaWitness_eq_eq
  [Field k]
  {n : ℕ}
  {i : Fin (n + 1)} :
-- imply
  (sigmaWitness i).card = i.val := by
-- proof
  apply GLnBuilding.card_sigmaWitness_eq i

/--
[finrank_biSup_span_singleton_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/RefinementCompatibility.lean)
-/
private lemma finrank_biSup_span_singleton_eq_card_eq
  [Field k]
  {n : ℕ}
  [AddCommGroup M]
  [Module k M]
  [Fintype ι]
  {v : ι → M}
  {S : Finset ι}
-- given
  (hli : LinearIndependent k v) :
-- imply
  Module.finrank k ↥(⨆ i ∈ S, k ∙ v i) = S.card := by
-- proof
  apply GLnBuilding.finrank_biSup_span_singleton_eq_card hli S

/--
[biSup_span_singleton_eq_of_le_of_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/RefinementCompatibility.lean)
-/
private lemma biSup_span_singleton_eq_of_le_of_finrank_eq
  [Field k]
  {n : ℕ}
  [AddCommGroup M]
  [Module k M]
  [Fintype ι]
  {v : ι → M}
  {S : Finset ι}
  {W : Submodule k M}
  [FiniteDimensional k W]
-- given
  (hli : LinearIndependent k v)
  (hle : (⨆ i ∈ S, k ∙ v i) ≤ W)
  (hfr : Module.finrank k W = S.card) :
-- imply
  (⨆ i ∈ S, k ∙ v i) = W := by
-- proof
  apply GLnBuilding.biSup_span_singleton_eq_of_le_of_finrank hli S W hle hfr


-- created on 2026-10-23
-- updated on 2026-10-24
