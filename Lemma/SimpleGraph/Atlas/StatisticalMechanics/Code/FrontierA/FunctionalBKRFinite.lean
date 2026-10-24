import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.FunctionalBKRFinite
open StatMech StatMech.FrontierA


/--
[mem_agreementFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFinite.lean)
-/
@[path]
private lemma mem_agreementFiber_eq
  [Fintype E]
  [DecidableEq E]
  {K : Set E}
  {omega eta : ConfigSpace E} :
-- imply
  eta ∈ agreementFiber K omega ↔ agreeOn K omega eta := by
-- proof
  apply StatMech.FrontierA.mem_agreementFiber

/--
[agreementFiber_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFinite.lean)
-/
@[path]
private lemma agreementFiber_nonempty_eq
  [Fintype E]
  [DecidableEq E]
  {K : Set E}
  {omega : ConfigSpace E} :
-- imply
  (agreementFiber K omega).Nonempty := by
-- proof
  apply StatMech.FrontierA.agreementFiber_nonempty K omega

/--
[cylinderMin_le_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFinite.lean)
-/
@[path]
private lemma cylinderMin_le_self_eq
  [Fintype E]
  [DecidableEq E]
  {f : ConfigSpace E → ℝ}
  {K : Set E}
  {omega : ConfigSpace E} :
-- imply
  cylinderMin f K omega ≤ f omega := by
-- proof
  apply StatMech.FrontierA.cylinderMin_le_self f K omega

/--
[cylinderMin_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFinite.lean)
-/
@[path]
private lemma cylinderMin_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {f : ConfigSpace E → ℝ}
  {K : Set E}
  {omega : ConfigSpace E}
-- given
  (hf : ∀ omega, 0 ≤ f omega) :
-- imply
  0 ≤ cylinderMin f K omega := by
-- proof
  apply StatMech.FrontierA.cylinderMin_nonneg hf K omega

/--
[cylinderMin_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFinite.lean)
-/
@[path]
private lemma cylinderMin_mono_eq
  [Fintype E]
  [DecidableEq E]
  {f g : ConfigSpace E → ℝ}
  {K : Set E}
  {omega : ConfigSpace E}
-- given
  (hfg : ∀ omega, f omega ≤ g omega) :
-- imply
  cylinderMin f K omega ≤ cylinderMin g K omega := by
-- proof
  apply StatMech.FrontierA.cylinderMin_mono hfg K omega

/--
[agreementFiber_eq_of_agreeOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFinite.lean)
-/
@[path]
private lemma agreementFiber_eq_of_agreeOn_eq
  [Fintype E]
  [DecidableEq E]
  {K : Set E}
  {omega omega' : ConfigSpace E}
-- given
  (h : agreeOn K omega omega') :
-- imply
  agreementFiber K omega = agreementFiber K omega' := by
-- proof
  apply StatMech.FrontierA.agreementFiber_eq_of_agreeOn h

/--
[cylinderMin_eq_of_agreeOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFinite.lean)
-/
@[path]
private lemma cylinderMin_eq_of_agreeOn_eq
  [Fintype E]
  [DecidableEq E]
  {f : ConfigSpace E → ℝ}
  {K : Set E}
  {omega omega' : ConfigSpace E}
-- given
  (h : agreeOn K omega omega') :
-- imply
  cylinderMin f K omega = cylinderMin f K omega' := by
-- proof
  apply StatMech.FrontierA.cylinderMin_eq_of_agreeOn f h

/--
[cylinderMin_eventIndicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFinite.lean)
-/
@[path]
private lemma cylinderMin_eventIndicator_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {K : Set E}
  {omega : ConfigSpace E} :
-- imply
  cylinderMin (eventIndicator A) K omega = eventIndicator {eta | OccursOn A K eta} omega := by
-- proof
  apply StatMech.FrontierA.cylinderMin_eventIndicator A K omega

/--
[mem_disjointCoordinatePairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFinite.lean)
-/
@[path]
private lemma mem_disjointCoordinatePairs_eq
  [Fintype E]
  [DecidableEq E]
  {pair : Set E × Set E} :
-- imply
  pair ∈ disjointCoordinatePairs E ↔ Disjoint pair.1 pair.2 := by
-- proof
  apply StatMech.FrontierA.mem_disjointCoordinatePairs

/--
[disjointCoordinatePairs_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFinite.lean)
-/
@[path]
private lemma disjointCoordinatePairs_nonempty_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  (disjointCoordinatePairs E).Nonempty := by
-- proof
  apply StatMech.FrontierA.disjointCoordinatePairs_nonempty

/--
[mem_dualDisjointOccurrence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFinite.lean)
-/
@[path]
private lemma mem_dualDisjointOccurrence_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {omega eta : ConfigSpace E} :
-- imply
  (omega, eta) ∈ dualDisjointOccurrence A B ↔ ∃ K L : Set E, Disjoint K L ∧ OccursOn A K omega ∧ OccursOn B L eta := by
-- proof
  apply StatMech.FrontierA.mem_dualDisjointOccurrence

/--
[dualDisjointOccurrence_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFinite.lean)
-/
@[path]
private lemma dualDisjointOccurrence_diagonal_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {omega : ConfigSpace E} :
-- imply
  (omega, omega) ∈ dualDisjointOccurrence A B ↔ omega ∈ disjointOccurrence A B := by
-- proof
  apply StatMech.FrontierA.dualDisjointOccurrence_diagonal A B omega

/--
[functionalDisjointMaxAt_eventIndicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFinite.lean)
-/
@[path]
private lemma functionalDisjointMaxAt_eventIndicator_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {omega eta : ConfigSpace E} :
-- imply
  functionalDisjointMaxAt (eventIndicator A) (eventIndicator B) omega eta = (dualDisjointOccurrence A B).indicator (fun _ => (1 : ℝ)) (omega, eta) := by
-- proof
  apply StatMech.FrontierA.functionalDisjointMaxAt_eventIndicator A B omega eta

/--
[functionalDisjointMax_eventIndicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFinite.lean)
-/
@[path]
private lemma functionalDisjointMax_eventIndicator_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {omega : ConfigSpace E} :
-- imply
  functionalDisjointMax (eventIndicator A) (eventIndicator B) omega = (disjointOccurrence A B).indicator (fun _ => (1 : ℝ)) omega := by
-- proof
  apply StatMech.FrontierA.functionalDisjointMax_eventIndicator A B omega


-- created on 2026-10-23
