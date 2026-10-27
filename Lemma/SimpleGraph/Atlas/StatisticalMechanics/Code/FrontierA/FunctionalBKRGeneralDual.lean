import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralDual.Part4
open Finset StatMech StatMech.FrontierA


/--
[dualOccurrence_to_twisted_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralDual.lean)
-/
@[path]
private lemma dualOccurrence_to_twisted_box_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {p : ConfigSpace E × ConfigSpace E}
  {k : ConfigSpace E × ConfigSpace E}
-- given
  (hp : p ∈ dualDisjointOccurrence A B)
  (hpk : orbitKey p = k) :
-- imply
  p.1 ∈ disjointOccurrence A (kssTwist k B) := by
-- proof
  apply StatMech.FrontierA.dualOccurrence_to_twisted_box hp hpk

/--
[rb3_slabCardAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralDual.lean)
-/
@[path]
private lemma rb3_slabCardAll_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  poc_SlabCardAll := by
-- proof
  apply StatMech.FrontierA.rb3_slabCardAll

/--
[imgOrbit_twist_eq_diagonalOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralDual.lean)
-/
@[path]
private lemma imgOrbit_twist_eq_diagonalOrbit_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {k : ConfigSpace E × ConfigSpace E} :
-- imply
  imgOrbit A (kssTwist k B) k = kssDiagonalOrbit A B k := by
-- proof
  apply StatMech.FrontierA.imgOrbit_twist_eq_diagonalOrbit A B k

/--
[kssDualOrbit_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralDual.lean)
-/
@[path]
private lemma kssDualOrbit_card_le_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {A B : Set (ConfigSpace (Fin n))}
  {k : ConfigSpace (Fin n) × ConfigSpace (Fin n)} :
-- imply
  #(kssDualOrbit A B k) ≤ #(kssDiagonalOrbit A B k) := by
-- proof
  apply StatMech.FrontierA.kssDualOrbit_card_le A B k

/--
[pairWeight_eq_of_sameOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralDual.lean)
-/
@[path]
private lemma pairWeight_eq_of_sameOrbit_eq
  [Fintype E]
  [DecidableEq E]
  {phi : E → Bool → ℝ}
  {p q : ConfigSpace E × ConfigSpace E}
-- given
  (h : sameOrbit p q) :
-- imply
  pweight phi q.1 * pweight phi q.2 = pweight phi p.1 * pweight phi p.2 := by
-- proof
  apply StatMech.FrontierA.pairWeight_eq_of_sameOrbit phi h

/--
[kssWeightInjection_fin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralDual.lean)
-/
@[path]
private lemma kssWeightInjection_fin_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {A B : Set (ConfigSpace (Fin n))} :
-- imply
  KSSWeightInjection A B := by
-- proof
  apply StatMech.FrontierA.kssWeightInjection_fin A B

/--
[dualBKR_wprob_fin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralDual.lean)
-/
@[path]
private lemma dualBKR_wprob_fin_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {phi : Fin n → Bool → ℝ}
  {A B : Set (ConfigSpace (Fin n))}
-- given
  (hphi0 : ∀ e b, 0 ≤ phi e b)
  (hphi1 : ∀ e, phi e false + phi e true = 1) :
-- imply
  dualWprob phi (dualDisjointOccurrence A B) ≤ wprob phi (A ∩ B) := by
-- proof
  apply StatMech.FrontierA.dualBKR_wprob_fin phi hphi0 hphi1 A B

/--
[dualWprob_inter_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralDual.lean)
-/
@[path]
private lemma dualWprob_inter_univ_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {phi : Fin n → Bool → ℝ}
  {C : Set (ConfigSpace (Fin n))}
-- given
  (hphi1 : ∀ e, phi e false + phi e true = 1) :
-- imply
  dualWprob phi (C ×ˢ (Set.univ : Set (ConfigSpace (Fin n)))) = wprob phi C := by
-- proof
  apply StatMech.FrontierA.dualWprob_inter_univ phi hphi1 C

/--
[dualPull_dualDisjointOccurrence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralDual.lean)
-/
@[path]
private lemma dualPull_dualDisjointOccurrence_eq
  [Fintype E]
  [DecidableEq E]
  {e : E ≃ F}
  {A B : Set (ConfigSpace E)} :
-- imply
  dualPull e (dualDisjointOccurrence A B) = dualDisjointOccurrence ((cfgEquiv e) ⁻¹' A) ((cfgEquiv e) ⁻¹' B) := by
-- proof
  apply StatMech.FrontierA.dualPull_dualDisjointOccurrence e A B

/--
[dualWprob_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralDual.lean)
-/
@[path]
private lemma dualWprob_transfer_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype F]
  [DecidableEq F]
  {e : E ≃ F}
  {phi : E → Bool → ℝ}
  {C : Set (ConfigSpace E × ConfigSpace E)} :
-- imply
  dualWprob phi C = dualWprob (fun y => phi (e.symm y)) (dualPull e C) := by
-- proof
  apply StatMech.FrontierA.dualWprob_transfer e phi C

/--
[dualBKR_wprob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralDual.lean)
-/
@[path]
private lemma dualBKR_wprob_eq
  [Fintype E]
  [DecidableEq E]
  {phi : E → Bool → ℝ}
  {A B : Set (ConfigSpace E)}
-- given
  (hphi0 : ∀ e b, 0 ≤ phi e b)
  (hphi1 : ∀ e, phi e false + phi e true = 1) :
-- imply
  dualWprob phi (dualDisjointOccurrence A B) ≤ wprob phi (A ∩ B) := by
-- proof
  apply StatMech.FrontierA.dualBKR_wprob phi hphi0 hphi1 A B

/--
[dualFunctionalBKR_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralDual.lean)
-/
@[path]
private lemma dualFunctionalBKR_real_eq
  [Fintype E]
  [DecidableEq E]
  {phi : E → Bool → ℝ}
  {f g : ConfigSpace E → ℝ}
-- given
  (hphi0 : ∀ e b, 0 ≤ phi e b)
  (hphi1 : ∀ e, phi e false + phi e true = 1)
  (hf0 : ∀ omega, 0 ≤ f omega)
  (hg0 : ∀ omega, 0 ≤ g omega) :
-- imply
  dualProductExpectation phi (fun pair => functionalDisjointMaxAt f g pair.1 pair.2) ≤ productExpectation phi (fun omega => f omega * g omega) := by
-- proof
  apply StatMech.FrontierA.dualFunctionalBKR_real phi hphi0 hphi1 f g hf0 hg0


-- created on 2026-10-23
