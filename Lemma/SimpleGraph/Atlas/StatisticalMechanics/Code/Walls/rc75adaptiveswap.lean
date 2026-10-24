import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc75adaptiveswap
open Finset StatMech StatMech.Walls


/--
[swapAt_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc75adaptiveswap.lean)
-/
@[path]
private lemma swapAt_involutive_eq
  {n : ℕ}
  {i : Fin n} :
-- imply
  Function.Involutive (swapAt i) := by
-- proof
  apply StatMech.Walls.swapAt_involutive i

/--
[swapAt_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc75adaptiveswap.lean)
-/
@[path]
private lemma swapAt_bijective_eq
  {n : ℕ}
  {i : Fin n} :
-- imply
  Function.Bijective (swapAt i) := by
-- proof
  apply StatMech.Walls.swapAt_bijective i

/--
[swapAt_off](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc75adaptiveswap.lean)
-/
@[path]
private lemma swapAt_off_eq
  {n : ℕ}
  {i : Fin n}
  {p : ConfigSpace (Fin n) × ConfigSpace (Fin n)}
  {j : Fin n}
-- given
  (hj : j ≠ i) :
-- imply
  (swapAt i p).1 j = p.1 j ∧ (swapAt i p).2 j = p.2 j := by
-- proof
  apply StatMech.Walls.swapAt_off i p hj

/--
[swapAt_on](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc75adaptiveswap.lean)
-/
@[path]
private lemma swapAt_on_eq
  {n : ℕ}
  {i : Fin n}
  {p : ConfigSpace (Fin n) × ConfigSpace (Fin n)} :
-- imply
  (swapAt i p).1 i = p.2 i ∧ (swapAt i p).2 i = p.1 i := by
-- proof
  apply StatMech.Walls.swapAt_on i p

/--
[swapAt_pair_perm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc75adaptiveswap.lean)
-/
@[path]
private lemma swapAt_pair_perm_eq
  {n : ℕ}
  {i : Fin n}
  {p : ConfigSpace (Fin n) × ConfigSpace (Fin n)}
  {j : Fin n} :
-- imply
  ((swapAt i p).1 j, (swapAt i p).2 j) = (p.1 j, p.2 j) ∨ ((swapAt i p).1 j, (swapAt i p).2 j) = (p.2 j, p.1 j) := by
-- proof
  apply StatMech.Walls.swapAt_pair_perm i p j

/--
[coordSwap_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc75adaptiveswap.lean)
-/
@[path]
private lemma coordSwap_involutive_eq
  {n : ℕ}
  {i : Fin n}
  [DecidablePred pred]
-- given
  (pred : ConfigSpace (Fin n) × ConfigSpace (Fin n) → Prop)
  (horb : ∀ p, pred (swapAt i p) ↔ pred p) :
-- imply
  Function.Involutive (coordSwap i pred) := by
-- proof
  apply StatMech.Walls.coordSwap_involutive i pred horb

/--
[coordSwap_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc75adaptiveswap.lean)
-/
@[path]
private lemma coordSwap_bijective_eq
  {n : ℕ}
  {i : Fin n}
  [DecidablePred pred]
-- given
  (pred : ConfigSpace (Fin n) × ConfigSpace (Fin n) → Prop)
  (horb : ∀ p, pred (swapAt i p) ↔ pred p) :
-- imply
  Function.Bijective (coordSwap i pred) := by
-- proof
  apply StatMech.Walls.coordSwap_bijective i pred horb

/--
[swapAt_mapsInto_of_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc75adaptiveswap.lean)
-/
@[path]
private lemma swapAt_mapsInto_of_witness_eq
  {n : ℕ}
  {A B : Set (ConfigSpace (Fin n))}
  {K : Finset (Fin n)}
  {i : Fin n}
  {ω₁ ω₂ : ConfigSpace (Fin n)}
-- given
  (hKi : Disjoint K {i})
  (hA : OccursOn A (K : Set (Fin n)) ω₁)
  (hB : OccursOn B ({i} : Finset (Fin n)) ω₁) :
-- imply
  (swapAt i (ω₁, ω₂)).1 ∈ A ∧ (swapAt i (ω₁, ω₂)).2 ∈ B := by
-- proof
  apply StatMech.Walls.swapAt_mapsInto_of_witness A B hKi ω₁ ω₂ hA hB

/--
[rc75_swapAtF_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc75adaptiveswap.lean)
-/
@[path]
private lemma rc75_swapAtF_involutive_eq
  {n : ℕ}
  {i : Fin 2} :
-- imply
  Function.Involutive (rc75_swapAtF i) := by
-- proof
  apply StatMech.Walls.rc75_swapAtF_involutive i

/--
[rc75_orbSwap_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc75adaptiveswap.lean)
-/
@[path]
private lemma rc75_orbSwap_involutive_eq
  {n : ℕ}
  {i : Fin 2}
  {c : Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2))} :
-- imply
  Function.Involutive (rc75_orbSwap i c) := by
-- proof
  apply StatMech.Walls.rc75_orbSwap_involutive i c

/--
[rc75_orbSwap_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc75adaptiveswap.lean)
-/
@[path]
private lemma rc75_orbSwap_bijective_eq
  {n : ℕ}
  {i : Fin 2}
  {c : Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2))} :
-- imply
  Function.Bijective (rc75_orbSwap i c) := by
-- proof
  apply StatMech.Walls.rc75_orbSwap_bijective i c

/--
[rc75_applyChoice_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc75adaptiveswap.lean)
-/
@[path]
private lemma rc75_applyChoice_card_eq
  {n : ℕ}
  {i : Fin 2}
  {c : Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2))}
  {img : Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2))} :
-- imply
  (rc75_applyChoice i c img).card = img.card := by
-- proof
  apply StatMech.Walls.rc75_applyChoice_card i c img

/--
[rc75_adaptive_succeeds_where_rc72_failed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc75adaptiveswap.lean)
-/
@[path]
private lemma rc75_adaptive_succeeds_where_rc72_failed_eq
  {n : ℕ} :
-- imply
  rc75_existsAdaptivePlan rc75_wA rc75_wB := by
-- proof
  apply StatMech.Walls.rc75_adaptive_succeeds_where_rc72_failed

/--
[rc75_disjOcc_wit_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc75adaptiveswap.lean)
-/
@[path]
private lemma rc75_disjOcc_wit_card_eq
  {n : ℕ} :
-- imply
  (rc75_disjOccF rc75_wA rc75_wB).card = 2 := by
-- proof
  apply StatMech.Walls.rc75_disjOcc_wit_card

/--
[rc75_adaptivePlan_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc75adaptiveswap.lean)
-/
@[path]
private lemma rc75_adaptivePlan_fin2_eq
  {n : ℕ} :
-- imply
  ∀ A B : Finset (ConfigSpace (Fin 2)), 2 ^ 2 * (rc75_disjOccF A B).card ≤ A.card * B.card → rc75_existsAdaptivePlan A B := by
-- proof
  apply StatMech.Walls.rc75_adaptivePlan_fin2

/--
[rc75_order_dependence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc75adaptiveswap.lean)
-/
@[path]
private lemma rc75_order_dependence_eq
  {n : ℕ} :
-- imply
  rc75_existsPlanOrder [1, 0] (rc75_sourceF rc75_wA rc75_wB) (rc75_prodF rc75_wA rc75_wB) ∧ ¬ rc75_existsPlanOrder [0, 1] (rc75_sourceF rc75_wA rc75_wB) (rc75_prodF rc75_wA rc75_wB) ∧ rc75_existsPlanOrder [0, 1] (rc75_sourceF rc75_gA rc75_gB) (rc75_prodF rc75_gA rc75_gB) ∧ ¬ rc75_existsPlanOrder [1, 0] (rc75_sourceF rc75_gA rc75_gB) (rc75_prodF rc75_gA rc75_gB) := by
-- proof
  apply StatMech.Walls.rc75_order_dependence

/--
[rc75_adaptivePlan_fin1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc75adaptiveswap.lean)
-/
@[path]
private lemma rc75_adaptivePlan_fin1_eq
  {n : ℕ} :
-- imply
  ∀ A B : Finset (ConfigSpace (Fin 1)), 2 ^ 1 * (rc75_disjOccF1 A B).card ≤ A.card * B.card → rc75_existsPlan1 (rc75_sourceF1 A B) (rc75_prodF1 A B) := by
-- proof
  apply StatMech.Walls.rc75_adaptivePlan_fin1

/--
[rc75_reimerWprobCore_of_boxUnionBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc75adaptiveswap.lean)
-/
@[path]
private lemma rc75_reimerWprobCore_of_boxUnionBound_eq
  {n : ℕ}
-- given
  (h : rc60_BoxUnionBound) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc75_reimerWprobCore_of_boxUnionBound h

/--
[rc75_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc75adaptiveswap.lean)
-/
@[path]
private lemma rc75_status_eq
  {n : ℕ} :
-- imply
  (∀ (i : Fin 2) (c img : Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2))), (rc75_applyChoice i c img).card = img.card) ∧ (∀ (m : ℕ) (i : Fin m) (pred : ConfigSpace (Fin m) × ConfigSpace (Fin m) → Prop) [DecidablePred pred], (∀ p, pred (swapAt i p) ↔ pred p) → Function.Bijective (coordSwap i pred)) ∧ (∀ (m : ℕ) (A B : Set (ConfigSpace (Fin m))) (K : Finset (Fin m)) (i : Fin m), Disjoint K {i} → ∀ (ω₁ ω₂ : ConfigSpace (Fin m)), OccursOn A (K : Set (Fin m)) ω₁ → OccursOn B ({i} : Finset (Fin m)) ω₁ → (swapAt i (ω₁, ω₂)).1 ∈ A ∧ (swapAt i (ω₁, ω₂)).2 ∈ B) ∧ (∀ A B : Finset (ConfigSpace (Fin 2)), 2 ^ 2 * (rc75_disjOccF A B).card ≤ A.card * B.card → rc75_existsAdaptivePlan A B) ∧ rc75_existsAdaptivePlan rc75_wA rc75_wB ∧ (rc75_existsPlanOrder [1, 0] (rc75_sourceF rc75_wA rc75_wB) (rc75_prodF rc75_wA rc75_wB) ∧ ¬ rc75_existsPlanOrder [0, 1] (rc75_sourceF rc75_wA rc75_wB) (rc75_prodF rc75_wA rc75_wB)) ∧ (rc60_BoxUnionBound → ReimerWprobCore) := by
-- proof
  apply StatMech.Walls.rc75_status


-- created on 2026-10-23
