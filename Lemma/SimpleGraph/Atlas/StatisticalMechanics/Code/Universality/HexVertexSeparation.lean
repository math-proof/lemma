import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexVertexSeparation
open StatMech StatMech.Universality


/--
[hexSep_passesThrough_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexSeparation.lean)
-/
@[path]
private lemma hexSep_passesThrough_congr_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {a : ℂ}
  {ts ts' : List ℤ}
  {z : ℂ}
-- given
  (h0 : ℤ)
  (h : ts = ts') :
-- imply
  PassesThrough a h0 ts z ↔ PassesThrough a h0 ts' z := by
-- proof
  apply StatMech.Universality.hexSep_passesThrough_congr a h0 ts ts' z h

/--
[hexSep_specialMidCount_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexSeparation.lean)
-/
@[path]
private lemma hexSep_specialMidCount_congr_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {a : ℂ}
  {v du : ℂ}
  {ts ts' : List ℤ}
-- given
  (h0 : ℤ)
  (h : ts = ts') :
-- imply
  specialMidCount a h0 v du ts = specialMidCount a h0 v du ts' := by
-- proof
  apply StatMech.Universality.hexSep_specialMidCount_congr a h0 v du ts ts' h

/--
[hexSep_passesThrough_r_of_count_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexSeparation.lean)
-/
@[path]
private lemma hexSep_passesThrough_r_of_count_three_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {ts : List ℤ}
-- given
  (hk : specialMidCount a h0 v du ts = 3) :
-- imply
  PassesThrough a h0 ts (v + hexOmega ^ 2 * du) := by
-- proof
  apply StatMech.Universality.hexSep_passesThrough_r_of_count_three ts hk

/--
[hexSep_passesThrough_q_of_count_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexSeparation.lean)
-/
@[path]
private lemma hexSep_passesThrough_q_of_count_three_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {ts : List ℤ}
-- given
  (hk : specialMidCount a h0 v du ts = 3) :
-- imply
  PassesThrough a h0 ts (v + hexOmega * du) := by
-- proof
  apply StatMech.Universality.hexSep_passesThrough_q_of_count_three ts hk

/--
[hexSep_neg_len_le_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexSeparation.lean)
-/
@[path]
private lemma hexSep_neg_len_le_sum_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {L : List ℤ}
-- given
  (hL : ∀ t ∈ L, t = 1 ∨ t = -1) :
-- imply
  -(L.length : ℤ) ≤ L.sum := by
-- proof
  apply StatMech.Universality.hexSep_neg_len_le_sum L hL

/--
[hexSep_legalSum_neg_four_len_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexSeparation.lean)
-/
@[path]
private lemma hexSep_legalSum_neg_four_len_ge_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {L : List ℤ}
-- given
  (hL : ∀ t ∈ L, t = 1 ∨ t = -1)
  (hsum : L.sum = -4) :
-- imply
  4 ≤ L.length := by
-- proof
  apply StatMech.Universality.hexSep_legalSum_neg_four_len_ge L hL hsum

/--
[hexSep_pairLq_length_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexSeparation.lean)
-/
@[path]
private lemma hexSep_pairLq_length_ge_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {E : HexVertexEnumeration region a h0 v du}
  {P : ℕ}
-- given
  (hP : P ∈ E.pairs) :
-- imply
  4 ≤ (E.pairLq P).length := by
-- proof
  apply StatMech.Universality.hexSep_pairLq_length_ge E P hP

/--
[hexSep_hqcross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexSeparation.lean)
-/
@[path]
private lemma hexSep_hqcross_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {E : HexVertexEnumeration region a h0 v du}
-- given
  (hS : HexVertexSeparated E) :
-- imply
  ∀ (P : E.pairs) (T : E.triplets), E.pairBase P ++ E.pairLq P ≠ E.tripBase T ++ [-1] := by
-- proof
  apply StatMech.Universality.hexSep_hqcross E hS

/--
[hexSep_hrcross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexSeparation.lean)
-/
@[path]
private lemma hexSep_hrcross_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {E : HexVertexEnumeration region a h0 v du}
-- given
  (hS : HexVertexSeparated E) :
-- imply
  ∀ (P : E.pairs) (T : E.triplets), E.pairBase P ++ E.pairLr P ≠ E.tripBase T ++ [1] := by
-- proof
  apply StatMech.Universality.hexSep_hrcross E hS

/--
[hexSep_hinj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexSeparation.lean)
-/
@[path]
private lemma hexSep_hinj_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {E : HexVertexEnumeration region a h0 v du}
-- given
  (hdu : du ≠ 0)
  (htinj : ∀ T1 T2 : E.triplets, E.tripBase T1 = E.tripBase T2 → T1 = T2)
  (hqinj : ∀ P1 P2 : E.pairs, E.pairBase P1 ++ E.pairLq P1 = E.pairBase P2 ++ E.pairLq P2 → P1 = P2)
  (hrinj : ∀ P1 P2 : E.pairs, E.pairBase P1 ++ E.pairLr P1 = E.pairBase P2 ++ E.pairLr P2 → P1 = P2)
  (hS : HexVertexSeparated E) :
-- imply
  Function.Injective fun x : Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) => E.slotTurns x.1 := by
-- proof
  apply StatMech.Universality.hexSep_hinj E hdu htinj hqinj hrinj hS

/--
[hexSep_relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexSeparation.lean)
-/
@[path]
private lemma hexSep_relation_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {E : HexVertexEnumeration region a h0 v du}
-- given
  (hdu : du ≠ 0)
  (hp : Summable fun ts => parafSummand region a h0 (v + du) (5/8) hexChi ts)
  (hq : Summable fun ts => parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi ts)
  (hr : Summable fun ts => parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts)
  (htinj : ∀ T1 T2 : E.triplets, E.tripBase T1 = E.tripBase T2 → T1 = T2)
  (hqinj : ∀ P1 P2 : E.pairs, E.pairBase P1 ++ E.pairLq P1 = E.pairBase P2 ++ E.pairLq P2 → P1 = P2)
  (hrinj : ∀ P1 P2 : E.pairs, E.pairBase P1 ++ E.pairLr P1 = E.pairBase P2 ++ E.pairLr P2 → P1 = P2)
  (hS : HexVertexSeparated E)
  (covp : ∀ ts ∈ Function.support (combinedSummand region a h0 v du), (ofTurns a h0 ts).EndsAt (v + du) → ∃ slot : SlotType E, E.slotTurns slot = ts)
  (covq : ∀ ts ∈ Function.support (combinedSummand region a h0 v du), (ofTurns a h0 ts).EndsAt (v + hexOmega * du) → ∃ slot : SlotType E, E.slotTurns slot = ts)
  (covr : ∀ ts ∈ Function.support (combinedSummand region a h0 v du), (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) → ∃ slot : SlotType E, E.slotTurns slot = ts) :
-- imply
  ((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi + ((v + hexOmega ^ 2 * du) - v) * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 := by
-- proof
  apply StatMech.Universality.hexSep_relation E hdu hp hq hr htinj hqinj hrinj hS covp covq covr

/--
[hexSep_separated_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexSeparation.lean)
-/
@[path]
private lemma hexSep_separated_empty_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {a : ℂ}
  {v du : ℂ}
-- given
  (h0 : ℤ)
  (hzero : ∀ z, parafObservable (fun _ => False) a h0 z (5/8) hexChi = 0) :
-- imply
  HexVertexSeparated (HexVertexEnumeration.empty (fun _ => False) a h0 v du hzero) where pairQ_count_three := by
-- proof
  apply StatMech.Universality.hexSep_separated_empty a h0 v du hzero


-- created on 2026-10-23
