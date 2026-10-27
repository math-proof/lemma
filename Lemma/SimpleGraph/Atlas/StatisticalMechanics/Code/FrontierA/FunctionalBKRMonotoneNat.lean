import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRMonotoneNat.Part4
open Finset StatMech StatMech.FrontierA


/--
[natUpperLevel_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneNat.lean)
-/
@[path]
private lemma natUpperLevel_isIncreasing_eq
  [Fintype E]
  [DecidableEq E]
  {F : ConfigSpace E -> ℕ}
  {k : ℕ}
-- given
  (hF : Monotone F) :
-- imply
  IsIncreasing (natUpperLevel F k) := by
-- proof
  apply StatMech.FrontierA.natUpperLevel_isIncreasing hF k

/--
[lt_natFunctionBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneNat.lean)
-/
@[path]
private lemma lt_natFunctionBound_eq
  [Fintype E]
  [DecidableEq E]
  {omega : ConfigSpace E}
-- given
  (F : ConfigSpace E -> ℕ) :
-- imply
  F omega < natFunctionBound F := by
-- proof
  apply StatMech.FrontierA.lt_natFunctionBound F omega

/--
[cylinderMin_natAsReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneNat.lean)
-/
@[path]
private lemma cylinderMin_natAsReal_eq
  [Fintype E]
  [DecidableEq E]
  {K : Set E}
  {omega : ConfigSpace E}
-- given
  (F : ConfigSpace E -> ℕ) :
-- imply
  cylinderMin (natAsReal F) K omega = cylinderMinNat F K omega := by
-- proof
  apply StatMech.FrontierA.cylinderMin_natAsReal F K omega

/--
[occursOn_natUpperLevel_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneNat.lean)
-/
@[path]
private lemma occursOn_natUpperLevel_iff_eq
  [Fintype E]
  [DecidableEq E]
  {k : ℕ}
  {K : Set E}
  {omega : ConfigSpace E}
-- given
  (F : ConfigSpace E -> ℕ) :
-- imply
  OccursOn (natUpperLevel F k) K omega ↔ k < cylinderMinNat F K omega := by
-- proof
  apply StatMech.FrontierA.occursOn_natUpperLevel_iff F k K omega

/--
[cylinderMinNat_le_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneNat.lean)
-/
@[path]
private lemma cylinderMinNat_le_self_eq
  [Fintype E]
  [DecidableEq E]
  {K : Set E}
  {omega : ConfigSpace E}
-- given
  (F : ConfigSpace E -> ℕ) :
-- imply
  cylinderMinNat F K omega ≤ F omega := by
-- proof
  apply StatMech.FrontierA.cylinderMinNat_le_self F K omega

/--
[cylinderMinNat_mul_le_levelBoxes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneNat.lean)
-/
@[path]
private lemma cylinderMinNat_mul_le_levelBoxes_eq
  [Fintype E]
  [DecidableEq E]
  {K L : Set E}
  {omega : ConfigSpace E}
-- given
  (F G : ConfigSpace E -> ℕ)
  (hKL : Disjoint K L) :
-- imply
  (cylinderMinNat F K omega : ℝ) * cylinderMinNat G L omega ≤ ∑ k ∈ Finset.range (natFunctionBound F), ∑ l ∈ Finset.range (natFunctionBound G), eventIndicator (disjointOccurrence (natUpperLevel F k) (natUpperLevel G l)) omega := by
-- proof
  apply StatMech.FrontierA.cylinderMinNat_mul_le_levelBoxes F G K L hKL omega

/--
[functionalDisjointMax_natAsReal_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneNat.lean)
-/
@[path]
private lemma functionalDisjointMax_natAsReal_le_eq
  [Fintype E]
  [DecidableEq E]
  {omega : ConfigSpace E}
-- given
  (F G : ConfigSpace E -> ℕ) :
-- imply
  functionalDisjointMax (natAsReal F) (natAsReal G) omega ≤ ∑ k ∈ Finset.range (natFunctionBound F), ∑ l ∈ Finset.range (natFunctionBound G), eventIndicator (disjointOccurrence (natUpperLevel F k) (natUpperLevel G l)) omega := by
-- proof
  apply StatMech.FrontierA.functionalDisjointMax_natAsReal_le F G omega

/--
[productExpectation_natAsReal_eq_levels](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneNat.lean)
-/
@[path]
private lemma productExpectation_natAsReal_eq_levels_eq
  [Fintype E]
  [DecidableEq E]
-- given
  (phi : E -> Bool -> ℝ)
  (F : ConfigSpace E -> ℕ) :
-- imply
  productExpectation phi (natAsReal F) = ∑ k ∈ Finset.range (natFunctionBound F), wprob phi (natUpperLevel F k) := by
-- proof
  apply StatMech.FrontierA.productExpectation_natAsReal_eq_levels phi F

/--
[functionalBKR_monotone_nat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneNat.lean)
-/
@[path]
private lemma functionalBKR_monotone_nat_eq
  [Fintype E]
  [DecidableEq E]
-- given
  (phi : E -> Bool -> ℝ)
  (hphi0 : ∀ e b, 0 ≤ phi e b)
  (hphi1 : ∀ e, phi e false + phi e true = 1)
  (F G : ConfigSpace E -> ℕ)
  (hF : Monotone F)
  (hG : Monotone G) :
-- imply
  productExpectation phi (functionalDisjointMax (natAsReal F) (natAsReal G)) ≤ productExpectation phi (natAsReal F) * productExpectation phi (natAsReal G) := by
-- proof
  apply StatMech.FrontierA.functionalBKR_monotone_nat phi hphi0 hphi1 F G hF hG


-- created on 2026-10-23
