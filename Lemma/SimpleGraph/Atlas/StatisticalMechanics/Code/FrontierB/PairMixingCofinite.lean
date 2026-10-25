import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.PairMixingCofinite
open MeasureTheory Set StatMech.ConfigSpace StatMech StatMech.FK


/--
[fmu_pairMixing_exists_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PairMixingCofinite.lean)
-/
@[path]
private lemma fmu_pairMixing_exists_not_mem_eq
  [CommGroup G]
  [MulAction G E]
  [Infinite G]
  [Countable E]
  [DecidableEq E]
  {mu : Measure (ConfigSpace E)}
  [IsProbabilityMeasure mu]
  {P : Finset (Finset E)}
  {K : Finset G}
  {delta : Real}
-- given
  (hti : IsTranslationInvariant (G := G) mu)
  (hmix : fmu_PairMixing (G := G) mu)
  (hdelta : 0 < delta) :
-- imply
  ∃ g : G, g ∉ K ∧ ∀ T ∈ P, ∀ T' ∈ P, abs (mu.real (fmu_multiOpen T ∩ (shift g : ConfigSpace E -> ConfigSpace E) ⁻¹' fmu_multiOpen T') - mu.real (fmu_multiOpen T) * mu.real (fmu_multiOpen T')) < delta := by
-- proof
  apply StatMech.FK.fmu_pairMixing_exists_not_mem hti hmix P K delta hdelta

/--
[fmu_pairMixing_exists_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PairMixingCofinite.lean)
-/
@[path]
private lemma fmu_pairMixing_exists_disjoint_eq
  [CommGroup G]
  [MulAction G E]
  [Infinite G]
  [Countable E]
  [DecidableEq E]
  {mu : Measure (ConfigSpace E)}
  [IsProbabilityMeasure mu]
  {P : Finset (Finset E)}
  {delta : Real}
-- given
  (hsolution : ∀ a b : E, {g : G | g • a = b}.Finite)
  (hti : IsTranslationInvariant (G := G) mu)
  (hmix : fmu_PairMixing (G := G) mu)
  (hdelta : 0 < delta) :
-- imply
  ∃ g : G, (∀ T ∈ P, ∀ T' ∈ P, Disjoint T (T'.image (fun e => g⁻¹ • e))) ∧ ∀ T ∈ P, ∀ T' ∈ P, abs (mu.real (fmu_multiOpen T ∩ (shift g : ConfigSpace E -> ConfigSpace E) ⁻¹' fmu_multiOpen T') - mu.real (fmu_multiOpen T) * mu.real (fmu_multiOpen T')) < delta := by
-- proof
  apply StatMech.FK.fmu_pairMixing_exists_disjoint hsolution hti hmix P delta hdelta

/--
[fmu_finsetExpansion_pairMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PairMixingCofinite.lean)
-/
@[path]
private lemma fmu_finsetExpansion_pairMixing_eq
  [CommGroup G]
  [MulAction G E]
  [Infinite G]
  [Countable E]
  [DecidableEq E]
  {mu : Measure (ConfigSpace E)}
  [IsProbabilityMeasure mu]
  [DecidableEq I]
  {indices : Finset I}
  {epsilon : Real}
-- given
  (hsolution : ∀ a b : E, {g : G | g • a = b}.Finite)
  (hti : IsTranslationInvariant (G := G) mu)
  (hmix : fmu_PairMixing (G := G) mu)
  (support : I -> Finset E)
  (c c' : I -> Real)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ g : G, (∀ i ∈ indices, ∀ j ∈ indices, Disjoint (support i) ((support j).image (fun e => g⁻¹ • e))) ∧ abs ((∫ omega, (∑ i ∈ indices, c i * fmu_moInd (support i) omega) * (∑ j ∈ indices, c' j * fmu_moInd (support j) (shift g omega)) ∂mu) - (∑ i ∈ indices, c i * mu.real (fmu_multiOpen (support i))) * (∑ j ∈ indices, c' j * mu.real (fmu_multiOpen (support j)))) < epsilon := by
-- proof
  apply StatMech.FK.fmu_finsetExpansion_pairMixing hsolution hti hmix indices support c c' epsilon hepsilon

/--
[fmu_finsetExpansion_family_pairMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PairMixingCofinite.lean)
-/
@[path]
private lemma fmu_finsetExpansion_family_pairMixing_eq
  [CommGroup G]
  [MulAction G E]
  [Infinite G]
  [Countable E]
  [DecidableEq E]
  {mu : Measure (ConfigSpace E)}
  [IsProbabilityMeasure mu]
  [DecidableEq I]
  {indices : Finset I}
  {epsilon : Real}
-- given
  (hsolution : ∀ a b : E, {g : G | g • a = b}.Finite)
  (hti : IsTranslationInvariant (G := G) mu)
  (hmix : fmu_PairMixing (G := G) mu)
  (support : I -> Finset E)
  (coeffs : Finset (I -> Real))
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ g : G, (∀ i ∈ indices, ∀ j ∈ indices, Disjoint (support i) ((support j).image (fun e => g⁻¹ • e))) ∧ ∀ c ∈ coeffs, ∀ c' ∈ coeffs, abs ((∫ omega, (∑ i ∈ indices, c i * fmu_moInd (support i) omega) * (∑ j ∈ indices, c' j * fmu_moInd (support j) (shift g omega)) ∂mu) - (∑ i ∈ indices, c i * mu.real (fmu_multiOpen (support i))) * (∑ j ∈ indices, c' j * mu.real (fmu_multiOpen (support j)))) < epsilon := by
-- proof
  apply StatMech.FK.fmu_finsetExpansion_family_pairMixing hsolution hti hmix indices support coeffs epsilon hepsilon


-- created on 2026-10-23
