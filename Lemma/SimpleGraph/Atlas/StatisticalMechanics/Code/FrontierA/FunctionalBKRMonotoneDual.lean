import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRMonotoneDual.Part3
open Finset StatMech StatMech.FrontierA


/--
[dualWprob_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneDual.lean)
-/
@[path]
private lemma dualWprob_mono_eq
  [Fintype E]
  [DecidableEq E]
  {phi : E → Bool → ℝ}
  {C D : Set (ConfigSpace E × ConfigSpace E)}
-- given
  (hphi0 : ∀ e b, 0 ≤ phi e b)
  (hCD : C ⊆ D) :
-- imply
  dualWprob phi C ≤ dualWprob phi D := by
-- proof
  apply StatMech.FrontierA.dualWprob_mono hphi0 hCD

/--
[dualWprob_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneDual.lean)
-/
@[path]
private lemma dualWprob_prod_eq
  [Fintype E]
  [DecidableEq E]
  {phi : E → Bool → ℝ}
  {A B : Set (ConfigSpace E)} :
-- imply
  dualWprob phi (A ×ˢ B) = wprob phi A * wprob phi B := by
-- proof
  apply StatMech.FrontierA.dualWprob_prod phi A B

/--
[dualDisjointOccurrence_subset_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneDual.lean)
-/
@[path]
private lemma dualDisjointOccurrence_subset_prod_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)} :
-- imply
  dualDisjointOccurrence A B ⊆ A ×ˢ B := by
-- proof
  apply StatMech.FrontierA.dualDisjointOccurrence_subset_prod A B

/--
[dualBKR_wprob_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneDual.lean)
-/
@[path]
private lemma dualBKR_wprob_increasing_eq
  [Fintype E]
  [DecidableEq E]
  {phi : E → Bool → ℝ}
  {A B : Set (ConfigSpace E)}
-- given
  (hphi0 : ∀ e b, 0 ≤ phi e b)
  (hphi1 : ∀ e, phi e false + phi e true = 1)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  dualWprob phi (dualDisjointOccurrence A B) ≤ wprob phi (A ∩ B) := by
-- proof
  apply StatMech.FrontierA.dualBKR_wprob_increasing phi hphi0 hphi1 hA hB

/--
[cylinderMinNat_mul_le_dualLevelBoxes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneDual.lean)
-/
@[path]
private lemma cylinderMinNat_mul_le_dualLevelBoxes_eq
  [Fintype E]
  [DecidableEq E]
  {F G : ConfigSpace E → ℕ}
  {K L : Set E}
  {omega eta : ConfigSpace E}
-- given
  (hKL : Disjoint K L) :
-- imply
  (cylinderMinNat F K omega : ℝ) * cylinderMinNat G L eta ≤ ∑ k ∈ Finset.range (natFunctionBound F), ∑ l ∈ Finset.range (natFunctionBound G), (dualDisjointOccurrence (natUpperLevel F k) (natUpperLevel G l)).indicator (fun _ => (1 : ℝ)) (omega, eta) := by
-- proof
  apply StatMech.FrontierA.cylinderMinNat_mul_le_dualLevelBoxes F G K L hKL omega eta

/--
[functionalDisjointMaxAt_natAsReal_le_dualLevels](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneDual.lean)
-/
@[path]
private lemma functionalDisjointMaxAt_natAsReal_le_dualLevels_eq
  [Fintype E]
  [DecidableEq E]
  {F G : ConfigSpace E → ℕ}
  {omega eta : ConfigSpace E} :
-- imply
  functionalDisjointMaxAt (natAsReal F) (natAsReal G) omega eta ≤ ∑ k ∈ Finset.range (natFunctionBound F), ∑ l ∈ Finset.range (natFunctionBound G), (dualDisjointOccurrence (natUpperLevel F k) (natUpperLevel G l)).indicator (fun _ => (1 : ℝ)) (omega, eta) := by
-- proof
  apply StatMech.FrontierA.functionalDisjointMaxAt_natAsReal_le_dualLevels F G omega eta

/--
[productExpectation_natAsReal_mul_eq_levelIntersections](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneDual.lean)
-/
@[path]
private lemma productExpectation_natAsReal_mul_eq_levelIntersections_eq
  [Fintype E]
  [DecidableEq E]
  {phi : E → Bool → ℝ}
  {F G : ConfigSpace E → ℕ} :
-- imply
  productExpectation phi (fun omega => natAsReal F omega * natAsReal G omega) = ∑ k ∈ Finset.range (natFunctionBound F), ∑ l ∈ Finset.range (natFunctionBound G), wprob phi (natUpperLevel F k ∩ natUpperLevel G l) := by
-- proof
  apply StatMech.FrontierA.productExpectation_natAsReal_mul_eq_levelIntersections phi F G

/--
[dualFunctionalBKR_monotone_nat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneDual.lean)
-/
@[path]
private lemma dualFunctionalBKR_monotone_nat_eq
  [Fintype E]
  [DecidableEq E]
  {phi : E → Bool → ℝ}
  {F G : ConfigSpace E → ℕ}
-- given
  (hphi0 : ∀ e b, 0 ≤ phi e b)
  (hphi1 : ∀ e, phi e false + phi e true = 1)
  (hF : Monotone F)
  (hG : Monotone G) :
-- imply
  dualProductExpectation phi (fun pair => functionalDisjointMaxAt (natAsReal F) (natAsReal G) pair.1 pair.2) ≤ productExpectation phi (fun omega => natAsReal F omega * natAsReal G omega) := by
-- proof
  apply StatMech.FrontierA.dualFunctionalBKR_monotone_nat phi hphi0 hphi1 F G hF hG

/--
[cylinderMin_mul_le_dualRealLevelBoxes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneDual.lean)
-/
@[path]
private lemma cylinderMin_mul_le_dualRealLevelBoxes_eq
  [Fintype E]
  [DecidableEq E]
  {f g : ConfigSpace E → ℝ}
  {K L : Set E}
  {omega eta : ConfigSpace E}
-- given
  (hf0 : ∀ omega, 0 ≤ f omega)
  (hg0 : ∀ omega, 0 ≤ g omega)
  (hKL : Disjoint K L) :
-- imply
  cylinderMin f K omega * cylinderMin g L eta ≤ ∑ layerF ∈ realLayerSet f, ∑ layerG ∈ realLayerSet g, layerF.2 * layerG.2 * (dualDisjointOccurrence (realUpperLevel f layerF.1) (realUpperLevel g layerG.1)).indicator (fun _ => (1 : ℝ)) (omega, eta) := by
-- proof
  apply StatMech.FrontierA.cylinderMin_mul_le_dualRealLevelBoxes hf0 hg0 K L hKL omega eta

/--
[functionalDisjointMaxAt_real_le_dualLevels](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneDual.lean)
-/
@[path]
private lemma functionalDisjointMaxAt_real_le_dualLevels_eq
  [Fintype E]
  [DecidableEq E]
  {f g : ConfigSpace E → ℝ}
  {omega eta : ConfigSpace E}
-- given
  (hf0 : ∀ omega, 0 ≤ f omega)
  (hg0 : ∀ omega, 0 ≤ g omega) :
-- imply
  functionalDisjointMaxAt f g omega eta ≤ ∑ layerF ∈ realLayerSet f, ∑ layerG ∈ realLayerSet g, layerF.2 * layerG.2 * (dualDisjointOccurrence (realUpperLevel f layerF.1) (realUpperLevel g layerG.1)).indicator (fun _ => (1 : ℝ)) (omega, eta) := by
-- proof
  apply StatMech.FrontierA.functionalDisjointMaxAt_real_le_dualLevels hf0 hg0 omega eta

/--
[productExpectation_real_mul_eq_levelIntersections](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneDual.lean)
-/
@[path]
private lemma productExpectation_real_mul_eq_levelIntersections_eq
  [Fintype E]
  [DecidableEq E]
  {phi : E → Bool → ℝ}
  {f g : ConfigSpace E → ℝ}
-- given
  (hf0 : ∀ omega, 0 ≤ f omega)
  (hg0 : ∀ omega, 0 ≤ g omega) :
-- imply
  productExpectation phi (fun omega => f omega * g omega) = ∑ layerF ∈ realLayerSet f, ∑ layerG ∈ realLayerSet g, layerF.2 * layerG.2 * wprob phi (realUpperLevel f layerF.1 ∩ realUpperLevel g layerG.1) := by
-- proof
  apply StatMech.FrontierA.productExpectation_real_mul_eq_levelIntersections phi hf0 hg0

/--
[dualFunctionalBKR_monotone_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneDual.lean)
-/
@[path]
private lemma dualFunctionalBKR_monotone_real_eq
  [Fintype E]
  [DecidableEq E]
  {phi : E → Bool → ℝ}
  {f g : ConfigSpace E → ℝ}
-- given
  (hphi0 : ∀ e b, 0 ≤ phi e b)
  (hphi1 : ∀ e, phi e false + phi e true = 1)
  (hf0 : ∀ omega, 0 ≤ f omega)
  (hg0 : ∀ omega, 0 ≤ g omega)
  (hf : Monotone f)
  (hg : Monotone g) :
-- imply
  dualProductExpectation phi (fun pair => functionalDisjointMaxAt f g pair.1 pair.2) ≤ productExpectation phi (fun omega => f omega * g omega) := by
-- proof
  apply StatMech.FrontierA.dualFunctionalBKR_monotone_real phi hphi0 hphi1 f g hf0 hg0 hf hg


-- created on 2026-10-23
