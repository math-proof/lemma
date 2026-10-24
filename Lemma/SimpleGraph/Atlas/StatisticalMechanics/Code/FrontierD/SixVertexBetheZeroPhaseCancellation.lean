import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseCancellation
open Finset StatMech StatMech.FrontierD


/--
[sixVertexBetheAmplitude_perturbedWordCoefficient_adjacent_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseCancellation.lean)
-/
@[path]
private lemma sixVertexBetheAmplitude_perturbedWordCoefficient_adjacent_cancel_eq
  {c : Real}
  {n : Nat}
  {p : Fin (n + 1) → Real}
  {ell : Fin (n + 1)}
  {eps : Real}
  {sigma : Equiv.Perm (Fin (n + 1))}
  {w : Finset (Fin (n + 1))}
  {i : Fin n}
-- given
  (hc : 2 < c)
  (hiM : i.castSucc ∉ w)
  (hiL : i.succ ∈ w)
  (ha : sigma i.castSucc ≠ ell)
  (hb : sigma i.succ ≠ ell)
  (hphase : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
-- imply
  sixVertexBetheAmplitude c p (sigma * Equiv.swap i.castSucc i.succ) * sixVertexBetheWordCoefficient c (fun j => sixVertexBethePhase (sixVertexBethePerturbRoot p ell eps j)) (sigma * Equiv.swap i.castSucc i.succ) w = -(sixVertexBetheAmplitude c p sigma * sixVertexBetheWordCoefficient c (fun j => sixVertexBethePhase (sixVertexBethePerturbRoot p ell eps j)) sigma w) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheAmplitude_perturbedWordCoefficient_adjacent_cancel hc p ell eps sigma w i hiM hiL ha hb hphase

/--
[sixVertexBethePerturbedWordTerm_adjacent_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseCancellation.lean)
-/
@[path]
private lemma sixVertexBethePerturbedWordTerm_adjacent_cancel_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {ell : Fin (n + 1)}
  {eps : Real}
  {x : Fin (n + 1) → Int}
  {w : Finset (Fin (n + 1))}
  {i : Fin n}
  {sigma : Equiv.Perm (Fin (n + 1))}
-- given
  (hc : 2 < c)
  (hiM : i.castSucc ∉ w)
  (hiL : i.succ ∈ w)
  (hphase : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1)
  (ha : sigma i.castSucc ≠ ell)
  (hb : sigma i.succ ≠ ell) :
-- imply
  sixVertexBethePerturbedWordTerm N c p ell eps x w (sigma * Equiv.swap i.castSucc i.succ) = -sixVertexBethePerturbedWordTerm N c p ell eps x w sigma := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePerturbedWordTerm_adjacent_cancel hc p ell eps x w i hiM hiL hphase sigma ha hb

/--
[sum_sixVertexBethePerturbedWordTerm_adjacent_away_zero_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseCancellation.lean)
-/
@[path]
private lemma sum_sixVertexBethePerturbedWordTerm_adjacent_away_zero_eq_zero_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {ell : Fin (n + 1)}
  {eps : Real}
  {x : Fin (n + 1) → Int}
  {w : Finset (Fin (n + 1))}
  {i : Fin n}
-- given
  (hc : 2 < c)
  (hiM : i.castSucc ∉ w)
  (hiL : i.succ ∈ w)
  (hphase : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
-- imply
  (∑ sigma : Equiv.Perm (Fin (n + 1)) with sigma i.castSucc ≠ ell ∧ sigma i.succ ≠ ell, sixVertexBethePerturbedWordTerm N c p ell eps x w sigma) = 0 := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexBethePerturbedWordTerm_adjacent_away_zero_eq_zero hc p ell eps x w i hiM hiL hphase

/--
[sixVertexBethePerturbedWordTerm_boundary_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseCancellation.lean)
-/
@[path]
private lemma sixVertexBethePerturbedWordTerm_boundary_cancel_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 2) → Real}
  {ell : Fin (n + 2)}
  {eps : Real}
  {x : Fin (n + 2) → Int}
  {w : Finset (Fin (n + 2))}
  {sigma : Equiv.Perm (Fin (n + 2))}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
  (haM : Fin.last (n + 1) ∉ w)
  (hbL : (0 : Fin (n + 2)) ∈ w)
  (hphase : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1)
  (ha : sigma (Fin.last (n + 1)) ≠ ell)
  (hb : sigma 0 ≠ ell) :
-- imply
  sixVertexBethePerturbedWordTerm N c p ell eps x w (sigma * Equiv.swap (Fin.last (n + 1)) 0) = -sixVertexBethePerturbedWordTerm N c p ell eps x w sigma := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePerturbedWordTerm_boundary_cancel hc p hp ell eps x w haM hbL hphase sigma ha hb

/--
[sum_sixVertexBethePerturbedWordTerm_boundary_away_zero_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseCancellation.lean)
-/
@[path]
private lemma sum_sixVertexBethePerturbedWordTerm_boundary_away_zero_eq_zero_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 2) → Real}
  {ell : Fin (n + 2)}
  {eps : Real}
  {x : Fin (n + 2) → Int}
  {w : Finset (Fin (n + 2))}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
  (haM : Fin.last (n + 1) ∉ w)
  (hbL : (0 : Fin (n + 2)) ∈ w)
  (hphase : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
-- imply
  (∑ sigma : Equiv.Perm (Fin (n + 2)) with sigma (Fin.last (n + 1)) ≠ ell ∧ sigma 0 ≠ ell, sixVertexBethePerturbedWordTerm N c p ell eps x w sigma) = 0 := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexBethePerturbedWordTerm_boundary_away_zero_eq_zero hc p hp ell eps x w haM hbL hphase

/--
[mem_sixVertexBetheMLBoundarySet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseCancellation.lean)
-/
@[path]
private lemma mem_sixVertexBetheMLBoundarySet_eq
  {n : Nat}
  {w : Finset (Fin (n + 1))}
  {i : Fin (n + 1)} :
-- imply
  i ∈ sixVertexBetheMLBoundarySet w ↔ i ∉ w ∧ finRotate (n + 1) i ∈ w := by
-- proof
  apply StatMech.FrontierD.mem_sixVertexBetheMLBoundarySet w i

/--
[exists_sixVertexBetheMLBoundary_away_of_one_lt_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseCancellation.lean)
-/
@[path]
private lemma exists_sixVertexBetheMLBoundary_away_of_one_lt_card_eq
  {n : Nat}
  {w : Finset (Fin (n + 1))}
  {a : Fin (n + 1)}
-- given
  (hcard : 1 < (sixVertexBetheMLBoundarySet w).card) :
-- imply
  ∃ i ∈ sixVertexBetheMLBoundarySet w, i ≠ a ∧ finRotate (n + 1) i ≠ a := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexBetheMLBoundary_away_of_one_lt_card w hcard a

/--
[sum_sixVertexBethePerturbedWordTerm_adjacent_fixed_zeroSlot_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseCancellation.lean)
-/
@[path]
private lemma sum_sixVertexBethePerturbedWordTerm_adjacent_fixed_zeroSlot_eq_zero_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {ell : Fin (n + 1)}
  {eps : Real}
  {x : Fin (n + 1) → Int}
  {w : Finset (Fin (n + 1))}
  {i : Fin n}
  {a : Fin (n + 1)}
-- given
  (hc : 2 < c)
  (hiM : i.castSucc ∉ w)
  (hiL : i.succ ∈ w)
  (ha : a ≠ i.castSucc)
  (hb : a ≠ i.succ)
  (hphase : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
-- imply
  (∑ sigma : Equiv.Perm (Fin (n + 1)) with sigma a = ell, sixVertexBethePerturbedWordTerm N c p ell eps x w sigma) = 0 := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexBethePerturbedWordTerm_adjacent_fixed_zeroSlot_eq_zero hc p ell eps x w i hiM hiL a ha hb hphase

/--
[sum_sixVertexBethePerturbedWordTerm_boundary_fixed_zeroSlot_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseCancellation.lean)
-/
@[path]
private lemma sum_sixVertexBethePerturbedWordTerm_boundary_fixed_zeroSlot_eq_zero_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 2) → Real}
  {ell : Fin (n + 2)}
  {eps : Real}
  {x : Fin (n + 2) → Int}
  {w : Finset (Fin (n + 2))}
  {a : Fin (n + 2)}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
  (hlastM : Fin.last (n + 1) ∉ w)
  (hzeroL : (0 : Fin (n + 2)) ∈ w)
  (ha : a ≠ Fin.last (n + 1))
  (hb : a ≠ 0)
  (hphase : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
-- imply
  (∑ sigma : Equiv.Perm (Fin (n + 2)) with sigma a = ell, sixVertexBethePerturbedWordTerm N c p ell eps x w sigma) = 0 := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexBethePerturbedWordTerm_boundary_fixed_zeroSlot_eq_zero hc p hp ell eps x w hlastM hzeroL a ha hb hphase

/--
[sum_sixVertexBethePerturbedWordTerm_eq_sum_fixed_zeroSlot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseCancellation.lean)
-/
@[path]
private lemma sum_sixVertexBethePerturbedWordTerm_eq_sum_fixed_zeroSlot_eq
  {N n : Nat}
  {c : Real}
  {p : Fin (n + 1) → Real}
  {ell : Fin (n + 1)}
  {eps : Real}
  {x : Fin (n + 1) → Int}
  {w : Finset (Fin (n + 1))} :
-- imply
  (∑ sigma : Equiv.Perm (Fin (n + 1)), sixVertexBethePerturbedWordTerm N c p ell eps x w sigma) = ∑ a : Fin (n + 1), ∑ sigma : Equiv.Perm (Fin (n + 1)) with sigma a = ell, sixVertexBethePerturbedWordTerm N c p ell eps x w sigma := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexBethePerturbedWordTerm_eq_sum_fixed_zeroSlot c p ell eps x w

/--
[sum_sixVertexBethePerturbedWordTerm_eq_zero_of_multiple_ML](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseCancellation.lean)
-/
@[path]
private lemma sum_sixVertexBethePerturbedWordTerm_eq_zero_of_multiple_ML_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 2) → Real}
  {ell : Fin (n + 2)}
  {eps : Real}
  {x : Fin (n + 2) → Int}
  {w : Finset (Fin (n + 2))}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
  (hcard : 1 < (sixVertexBetheMLBoundarySet w).card)
  (hphase : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
-- imply
  (∑ sigma : Equiv.Perm (Fin (n + 2)), sixVertexBethePerturbedWordTerm N c p ell eps x w sigma) = 0 := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexBethePerturbedWordTerm_eq_zero_of_multiple_ML hc p hp ell eps x w hcard hphase


-- created on 2026-10-23
