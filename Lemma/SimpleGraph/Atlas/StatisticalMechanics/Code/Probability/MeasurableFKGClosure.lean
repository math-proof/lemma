import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Probability.MeasurableFKGClosure
open Filter MeasureTheory Set Topology StatMech


/--
[isClopen_of_dependsOn_finset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MeasurableFKGClosure.lean)
-/
@[path]
private lemma isClopen_of_dependsOn_finset_eq
  [DecidableEq E]
  [Countable E]
  {A : Set (ConfigSpace E)}
  {F : Finset E}
-- given
  (hA : DependsOn A (F : Set E)) :
-- imply
  IsClopen A := by
-- proof
  apply StatMech.isClopen_of_dependsOn_finset A F hA

/--
[finiteUpwardHull_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MeasurableFKGClosure.lean)
-/
@[path]
private lemma finiteUpwardHull_dependsOn_eq
  [DecidableEq E]
  [Countable E]
  {F : Finset E}
  {A : Set (ConfigSpace E)} :
-- imply
  DependsOn (finiteUpwardHull F A) (F : Set E) := by
-- proof
  apply StatMech.finiteUpwardHull_dependsOn F A

/--
[finiteUpwardHull_isClopen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MeasurableFKGClosure.lean)
-/
@[path]
private lemma finiteUpwardHull_isClopen_eq
  [DecidableEq E]
  [Countable E]
  {F : Finset E}
  {A : Set (ConfigSpace E)} :
-- imply
  IsClopen (finiteUpwardHull F A) := by
-- proof
  apply StatMech.finiteUpwardHull_isClopen F A

/--
[finiteUpwardHull_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MeasurableFKGClosure.lean)
-/
@[path]
private lemma finiteUpwardHull_isIncreasing_eq
  [DecidableEq E]
  [Countable E]
  {F : Finset E}
  {A : Set (ConfigSpace E)} :
-- imply
  IsIncreasing (finiteUpwardHull F A) := by
-- proof
  apply StatMech.finiteUpwardHull_isIncreasing F A

/--
[subset_finiteUpwardHull](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MeasurableFKGClosure.lean)
-/
@[path]
private lemma subset_finiteUpwardHull_eq
  [DecidableEq E]
  [Countable E]
  {F : Finset E}
  {A : Set (ConfigSpace E)} :
-- imply
  A ⊆ finiteUpwardHull F A := by
-- proof
  apply StatMech.subset_finiteUpwardHull F A

/--
[isClosed_Iic_config](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MeasurableFKGClosure.lean)
-/
@[path]
private lemma isClosed_Iic_config_eq
  [DecidableEq E]
  [Countable E]
  {x : ConfigSpace E} :
-- imply
  IsClosed (Set.Iic x) := by
-- proof
  apply StatMech.isClosed_Iic_config x

/--
[finiteUpwardHull_not_mem_of_disjoint_Iic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MeasurableFKGClosure.lean)
-/
@[path]
private lemma finiteUpwardHull_not_mem_of_disjoint_Iic_eq
  [DecidableEq E]
  [Countable E]
  {F : Finset E}
  {A : Set (ConfigSpace E)}
  {x : ConfigSpace E}
-- given
  (hA : DependsOn A (F : Set E))
  (hdisjoint : Disjoint A (Set.Iic x)) :
-- imply
  x ∉ finiteUpwardHull F A := by
-- proof
  apply StatMech.finiteUpwardHull_not_mem_of_disjoint_Iic F A x hA hdisjoint

/--
[exists_increasing_isClopen_superset_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MeasurableFKGClosure.lean)
-/
@[path]
private lemma exists_increasing_isClopen_superset_not_mem_eq
  [DecidableEq E]
  [Countable E]
  {C : Set (ConfigSpace E)}
  {x : ConfigSpace E}
-- given
  (hCclosed : IsClosed C)
  (hCinc : IsIncreasing C)
  (hx : x ∉ C) :
-- imply
  ∃ H : Set (ConfigSpace E), IsClopen H ∧ IsIncreasing H ∧ C ⊆ H ∧ x ∉ H := by
-- proof
  apply StatMech.exists_increasing_isClopen_superset_not_mem C hCclosed hCinc hx

/--
[exists_antitone_isClopen_isIncreasing_iInter_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MeasurableFKGClosure.lean)
-/
@[path]
private lemma exists_antitone_isClopen_isIncreasing_iInter_eq_eq
  [DecidableEq E]
  [Countable E]
  {C : Set (ConfigSpace E)}
-- given
  (hCclosed : IsClosed C)
  (hCinc : IsIncreasing C) :
-- imply
  ∃ A : Nat → Set (ConfigSpace E), Antitone A ∧ (∀ n, IsClopen (A n)) ∧ (∀ n, IsIncreasing (A n)) ∧ (⋂ n, A n) = C := by
-- proof
  apply StatMech.exists_antitone_isClopen_isIncreasing_iInter_eq C hCclosed hCinc

/--
[configUpwardClosure_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MeasurableFKGClosure.lean)
-/
@[path]
private lemma configUpwardClosure_isIncreasing_eq
  [DecidableEq E]
  [Countable E]
  {K : Set (ConfigSpace E)} :
-- imply
  IsIncreasing (configUpwardClosure K) := by
-- proof
  apply StatMech.configUpwardClosure_isIncreasing K

/--
[subset_configUpwardClosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MeasurableFKGClosure.lean)
-/
@[path]
private lemma subset_configUpwardClosure_eq
  [DecidableEq E]
  [Countable E]
  {K : Set (ConfigSpace E)} :
-- imply
  K ⊆ configUpwardClosure K := by
-- proof
  apply StatMech.subset_configUpwardClosure K

/--
[configUpwardClosure_subset_of_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MeasurableFKGClosure.lean)
-/
@[path]
private lemma configUpwardClosure_subset_of_isIncreasing_eq
  [DecidableEq E]
  [Countable E]
  {K A : Set (ConfigSpace E)}
-- given
  (hKA : K ⊆ A)
  (hA : IsIncreasing A) :
-- imply
  configUpwardClosure K ⊆ A := by
-- proof
  apply StatMech.configUpwardClosure_subset_of_isIncreasing hKA hA

/--
[configOrder_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MeasurableFKGClosure.lean)
-/
@[path]
private lemma configOrder_isClosed_eq
  [DecidableEq E]
  [Countable E] :
-- imply
  IsClosed {z : ConfigSpace E × ConfigSpace E | z.1 ≤ z.2} := by
-- proof
  apply StatMech.configOrder_isClosed

/--
[configUpwardClosure_isCompact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MeasurableFKGClosure.lean)
-/
@[path]
private lemma configUpwardClosure_isCompact_eq
  [DecidableEq E]
  [Countable E]
  {K : Set (ConfigSpace E)}
-- given
  (hK : IsCompact K) :
-- imply
  IsCompact (configUpwardClosure K) := by
-- proof
  apply StatMech.configUpwardClosure_isCompact hK

/--
[configUpwardClosure_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MeasurableFKGClosure.lean)
-/
@[path]
private lemma configUpwardClosure_isClosed_eq
  [DecidableEq E]
  [Countable E]
  {K : Set (ConfigSpace E)}
-- given
  (hK : IsCompact K) :
-- imply
  IsClosed (configUpwardClosure K) := by
-- proof
  apply StatMech.configUpwardClosure_isClosed hK

/--
[fkg_isClosed_of_isClopen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MeasurableFKGClosure.lean)
-/
@[path]
private lemma fkg_isClosed_of_isClopen_eq
  [DecidableEq E]
  [Countable E]
  {mu : Measure (ConfigSpace E)}
  [IsProbabilityMeasure mu]
  {C D : Set (ConfigSpace E)}
-- given
  (hclopen : ∀ C D : Set (ConfigSpace E), IsClopen C → IsClopen D → IsIncreasing C → IsIncreasing D → mu.real C * mu.real D ≤ mu.real (C ∩ D))
  (hCclosed : IsClosed C)
  (hDclosed : IsClosed D)
  (hCinc : IsIncreasing C)
  (hDinc : IsIncreasing D) :
-- imply
  mu.real C * mu.real D ≤ mu.real (C ∩ D) := by
-- proof
  apply StatMech.fkg_isClosed_of_isClopen mu hclopen hCclosed hDclosed hCinc hDinc

/--
[exists_compact_subset_measureReal_lt_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MeasurableFKGClosure.lean)
-/
@[path]
private lemma exists_compact_subset_measureReal_lt_add_eq
  [DecidableEq E]
  [Countable E]
  {mu : Measure (ConfigSpace E)}
  [IsProbabilityMeasure mu]
  {A : Set (ConfigSpace E)}
  {epsilon : Real}
-- given
  (hA : MeasurableSet A)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ K : Set (ConfigSpace E), K ⊆ A ∧ IsCompact K ∧ mu.real A < mu.real K + epsilon := by
-- proof
  apply StatMech.exists_compact_subset_measureReal_lt_add mu hA hepsilon

/--
[fkg_measurable_of_isClopen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MeasurableFKGClosure.lean)
-/
@[path]
private lemma fkg_measurable_of_isClopen_eq
  [DecidableEq E]
  [Countable E]
  {mu : Measure (ConfigSpace E)}
  [IsProbabilityMeasure mu]
  {A B : Set (ConfigSpace E)}
-- given
  (hclopen : ∀ C D : Set (ConfigSpace E), IsClopen C → IsClopen D → IsIncreasing C → IsIncreasing D → mu.real C * mu.real D ≤ mu.real (C ∩ D))
  (hAmeas : MeasurableSet A)
  (hBmeas : MeasurableSet B)
  (hAinc : IsIncreasing A)
  (hBinc : IsIncreasing B) :
-- imply
  mu.real A * mu.real B ≤ mu.real (A ∩ B) := by
-- proof
  apply StatMech.fkg_measurable_of_isClopen mu hclopen A B hAmeas hBmeas hAinc hBinc


-- created on 2026-10-23
