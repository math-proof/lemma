import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexCyclicVertexPartition.Part9
open StatMech StatMech.Universality


/--
[hexCyclicSucc_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean)
-/
@[path]
private lemma hexCyclicSucc_pred_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {j : Fin 3} :
-- imply
  hexCyclicSucc (hexCyclicPred j) = j := by
-- proof
  apply StatMech.Universality.hexCyclicSucc_pred j

/--
[hexCyclicPred_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean)
-/
@[path]
private lemma hexCyclicPred_succ_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {j : Fin 3} :
-- imply
  hexCyclicPred (hexCyclicSucc j) = j := by
-- proof
  apply StatMech.Universality.hexCyclicPred_succ j

/--
[hexCyclicSucc_mid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean)
-/
@[path]
private lemma hexCyclicSucc_mid_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {v du : ℂ}
  {j : Fin 3} :
-- imply
  labelMid v du (hexCyclicSucc j) = v + hexOmega * (labelMid v du j - v) := by
-- proof
  apply StatMech.Universality.hexCyclicSucc_mid v du j

/--
[hexCyclicPred_mid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean)
-/
@[path]
private lemma hexCyclicPred_mid_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {v du : ℂ}
  {j : Fin 3} :
-- imply
  labelMid v du (hexCyclicPred j) = v + hexOmega ^ 2 * (labelMid v du j - v) := by
-- proof
  apply StatMech.Universality.hexCyclicPred_mid v du j

/--
[HexCyclicTriplet.contribution_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean)
-/
@[path]
private lemma contribution_zero_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {C : HexCyclicTriplet region a h0 v du} :
-- imply
  (labelMid v du C.baseLabel - v) * parafSummand region a h0 (labelMid v du C.baseLabel) (5 / 8) hexChi C.base + (labelMid v du (hexCyclicSucc C.baseLabel) - v) * parafSummand region a h0 (labelMid v du (hexCyclicSucc C.baseLabel)) (5 / 8) hexChi (C.base ++ [-1]) + (labelMid v du (hexCyclicPred C.baseLabel) - v) * parafSummand region a h0 (labelMid v du (hexCyclicPred C.baseLabel)) (5 / 8) hexChi (C.base ++ [1]) = 0 := by
-- proof
  apply StatMech.Universality.HexCyclicTriplet.contribution_zero C

/--
[hexCyclic_midAccum_append_single](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean)
-/
@[path]
private lemma hexCyclic_midAccum_append_single_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {m : ℂ}
  {ts : List ℤ}
-- given
  (h t : ℤ) :
-- imply
  hexInfra_midAccum m h (ts ++ [t]) = hexInfra_midAccum m h ts + halfStep (hexInfra_headAccum h ts) + halfStep (hexInfra_headAccum h ts + t) := by
-- proof
  apply StatMech.Universality.hexCyclic_midAccum_append_single m h t ts

/--
[hexCyclic_midsAux_append_single](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean)
-/
@[path]
private lemma hexCyclic_midsAux_append_single_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {m : ℂ}
  {ts : List ℤ}
-- given
  (h t : ℤ) :
-- imply
  midsAux m h (ts ++ [t]) = midsAux m h ts ++ [hexInfra_midAccum m h ts + halfStep (hexInfra_headAccum h ts) + halfStep (hexInfra_headAccum h ts + t)] := by
-- proof
  apply StatMech.Universality.hexCyclic_midsAux_append_single m h t ts

/--
[hexCyclic_verticesAux_append_single](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean)
-/
@[path]
private lemma hexCyclic_verticesAux_append_single_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {m : ℂ}
  {ts : List ℤ}
-- given
  (h t : ℤ) :
-- imply
  verticesAux m h (ts ++ [t]) = verticesAux m h ts ++ [hexInfra_midAccum m h ts + halfStep (hexInfra_headAccum h ts) + halfStep (hexInfra_headAccum h ts + t) + halfStep (hexInfra_headAccum h ts + t)] := by
-- proof
  apply StatMech.Universality.hexCyclic_verticesAux_append_single m h t ts

/--
[hexCyclic_staysIn_concat_single_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean)
-/
@[path]
private lemma hexCyclic_staysIn_concat_single_iff_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {a : ℂ}
  {ts : List ℤ}
-- given
  (region : ℂ → Prop)
  (h0 t : ℤ) :
-- imply
  (ofTurns a h0 (ts ++ [t])).StaysIn region ↔ (ofTurns a h0 ts).StaysIn region ∧ region (hexCyclicNewMid a h0 ts t) := by
-- proof
  apply StatMech.Universality.hexCyclic_staysIn_concat_single_iff region a h0 t ts

/--
[hexCyclic_isSAW_concat_single_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean)
-/
@[path]
private lemma hexCyclic_isSAW_concat_single_iff_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 t : ℤ) :
-- imply
  (ofTurns a h0 (ts ++ [t])).IsSAW ↔ (ofTurns a h0 ts).IsSAW ∧ hexCyclicNewVertex a h0 ts t ∉ (ofTurns a h0 ts).vertices := by
-- proof
  apply StatMech.Universality.hexCyclic_isSAW_concat_single_iff a h0 t ts

/--
[hexCyclic_legalTurns_concat_single](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean)
-/
@[path]
private lemma hexCyclic_legalTurns_concat_single_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 t : ℤ)
  (hbase : (ofTurns a h0 ts).LegalTurns)
  (ht : t = 1 ∨ t = -1) :
-- imply
  (ofTurns a h0 (ts ++ [t])).LegalTurns := by
-- proof
  apply StatMech.Universality.hexCyclic_legalTurns_concat_single a h0 t ts hbase ht

/--
[HexCyclicLaunch.succ_newMid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean)
-/
@[path]
private lemma succ_newMid_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {j : Fin 3}
  {ts : List ℤ}
  {L : HexCyclicLaunch a h0 v du j ts} :
-- imply
  hexCyclicNewMid a h0 ts (-1) = labelMid v du (hexCyclicSucc j) := by
-- proof
  apply StatMech.Universality.HexCyclicLaunch.succ_newMid L

/--
[HexCyclicLaunch.pred_newMid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean)
-/
@[path]
private lemma pred_newMid_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {j : Fin 3}
  {ts : List ℤ}
  {L : HexCyclicLaunch a h0 v du j ts} :
-- imply
  hexCyclicNewMid a h0 ts 1 = labelMid v du (hexCyclicPred j) := by
-- proof
  apply StatMech.Universality.HexCyclicLaunch.pred_newMid L

/--
[HexCyclicLaunch.succ_endsAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean)
-/
@[path]
private lemma succ_endsAt_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {j : Fin 3}
  {ts : List ℤ}
  {L : HexCyclicLaunch a h0 v du j ts} :
-- imply
  (ofTurns a h0 (ts ++ [-1])).EndsAt (labelMid v du (hexCyclicSucc j)) := by
-- proof
  apply StatMech.Universality.HexCyclicLaunch.succ_endsAt L

/--
[HexCyclicLaunch.pred_endsAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean)
-/
@[path]
private lemma pred_endsAt_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {j : Fin 3}
  {ts : List ℤ}
  {L : HexCyclicLaunch a h0 v du j ts} :
-- imply
  (ofTurns a h0 (ts ++ [1])).EndsAt (labelMid v du (hexCyclicPred j)) := by
-- proof
  apply StatMech.Universality.HexCyclicLaunch.pred_endsAt L

/--
[mem_hexVisitClassFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean)
-/
@[path]
private lemma mem_hexVisitClassFinset_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {R : HexFiniteRegion}
  {a : ℂ}
  {v du : ℂ}
  {k : ℕ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hdu : du ≠ 0) :
-- imply
  ts ∈ hexVisitClassFinset R a h0 v du hdu k ↔ ts ∈ R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu ∧ specialMidCount a h0 v du ts = k := by
-- proof
  apply StatMech.Universality.mem_hexVisitClassFinset R a h0 v du hdu k ts

/--
[specialMidCount_le_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean)
-/
@[path]
private lemma specialMidCount_le_three_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {a : ℂ}
  {v du : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ) :
-- imply
  specialMidCount a h0 v du ts ≤ 3 := by
-- proof
  apply StatMech.Universality.specialMidCount_le_three a h0 v du ts

/--
[support_specialMidCount_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean)
-/
@[path]
private lemma support_specialMidCount_pos_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {ts : List ℤ}
-- given
  (hts : ts ∈ Function.support (combinedSummand region a h0 v du)) :
-- imply
  0 < specialMidCount a h0 v du ts := by
-- proof
  apply StatMech.Universality.support_specialMidCount_pos ts hts

/--
[support_specialMidCount_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean)
-/
@[path]
private lemma support_specialMidCount_cases_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {ts : List ℤ}
-- given
  (hts : ts ∈ Function.support (combinedSummand region a h0 v du)) :
-- imply
  specialMidCount a h0 v du ts = 1 ∨ specialMidCount a h0 v du ts = 2 ∨ specialMidCount a h0 v du ts = 3 := by
-- proof
  apply StatMech.Universality.support_specialMidCount_cases ts hts

/--
[supportFinset_eq_visitClasses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean)
-/
@[path]
private lemma supportFinset_eq_visitClasses_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {R : HexFiniteRegion}
  {a : ℂ}
  {v du : ℂ}
-- given
  (h0 : ℤ)
  (hdu : du ≠ 0) :
-- imply
  R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu = hexVisitClassFinset R a h0 v du hdu 1 ∪ hexVisitClassFinset R a h0 v du hdu 2 ∪ hexVisitClassFinset R a h0 v du hdu 3 := by
-- proof
  apply StatMech.Universality.supportFinset_eq_visitClasses R a h0 v du hdu

/--
[hexVisitClassFinset_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean)
-/
@[path]
private lemma hexVisitClassFinset_disjoint_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {R : HexFiniteRegion}
  {a : ℂ}
  {v du : ℂ}
  {k l : ℕ}
-- given
  (h0 : ℤ)
  (hdu : du ≠ 0)
  (hkl : k ≠ l) :
-- imply
  Disjoint (hexVisitClassFinset R a h0 v du hdu k) (hexVisitClassFinset R a h0 v du hdu l) := by
-- proof
  apply StatMech.Universality.hexVisitClassFinset_disjoint R a h0 v du hdu hkl

/--
[hexDecodedTurns_encode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean)
-/
@[path]
private lemma hexDecodedTurns_encode_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {ts : List ℤ} :
-- imply
  hexDecodedTurns (Encodable.encode ts) = ts := by
-- proof
  apply StatMech.Universality.hexDecodedTurns_encode ts

/--
[mem_hexKOneBaseTurns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean)
-/
@[path]
private lemma mem_hexKOneBaseTurns_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {R : HexFiniteRegion}
  {a : ℂ}
  {v du : ℂ}
  {j : Fin 3}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hdu : du ≠ 0) :
-- imply
  ts ∈ hexKOneBaseTurns R a h0 v du hdu j ↔ ts ∈ R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu ∧ specialMidCount a h0 v du ts = 1 ∧ (ofTurns a h0 ts).EndsAt (labelMid v du j) := by
-- proof
  apply StatMech.Universality.mem_hexKOneBaseTurns R a h0 v du hdu j ts

/--
[hexKOneBase_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean)
-/
@[path]
private lemma hexKOneBase_valid_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {R : HexFiniteRegion}
  {a : ℂ}
  {v du : ℂ}
  {j : Fin 3}
  {n : ℕ}
-- given
  (h0 : ℤ)
  (hdu : du ≠ 0)
  (hn : n ∈ hexKOneBaseIndices R a h0 v du hdu j) :
-- imply
  (ofTurns a h0 (hexDecodedTurns n)).IsLegalSAW ∧ (ofTurns a h0 (hexDecodedTurns n)).StaysIn R.inRegion ∧ (ofTurns a h0 (hexDecodedTurns n)).EndsAt (labelMid v du j) ∧ specialMidCount a h0 v du (hexDecodedTurns n) = 1 := by
-- proof
  apply StatMech.Universality.hexKOneBase_valid R a h0 v du hdu j n hn

/--
[hexKOneBase_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean)
-/
@[path]
private lemma hexKOneBase_injective_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {R : HexFiniteRegion}
  {a : ℂ}
  {v du : ℂ}
  {j : Fin 3}
-- given
  (h0 : ℤ)
  (hdu : du ≠ 0) :
-- imply
  ∀ n₁ n₂ : hexKOneBaseIndices R a h0 v du hdu j, hexDecodedTurns n₁ = hexDecodedTurns n₂ → n₁ = n₂ := by
-- proof
  apply StatMech.Universality.hexKOneBase_injective R a h0 v du hdu j

/--
[hexKOneBase_classify](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean)
-/
@[path]
private lemma hexKOneBase_classify_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {R : HexFiniteRegion}
  {a : ℂ}
  {v du : ℂ}
  {j : Fin 3}
-- given
  (h0 : ℤ)
  (hdu : du ≠ 0) :
-- imply
  ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du), specialMidCount a h0 v du ts = 1 → (ofTurns a h0 ts).EndsAt (labelMid v du j) → ∃ n : ℕ, n ∈ hexKOneBaseIndices R a h0 v du hdu j ∧ hexDecodedTurns n = ts := by
-- proof
  apply StatMech.Universality.hexKOneBase_classify R a h0 v du hdu j

/--
[hexVisitClass_one_eq_cyclicBases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean)
-/
@[path]
private lemma hexVisitClass_one_eq_cyclicBases_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {R : HexFiniteRegion}
  {a : ℂ}
  {v du : ℂ}
-- given
  (h0 : ℤ)
  (hdu : du ≠ 0) :
-- imply
  hexVisitClassFinset R a h0 v du hdu 1 = hexKOneBaseTurns R a h0 v du hdu 0 ∪ hexKOneBaseTurns R a h0 v du hdu 1 ∪ hexKOneBaseTurns R a h0 v du hdu 2 := by
-- proof
  apply StatMech.Universality.hexVisitClass_one_eq_cyclicBases R a h0 v du hdu

/--
[hexKOneBaseTurns_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean)
-/
@[path]
private lemma hexKOneBaseTurns_disjoint_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {R : HexFiniteRegion}
  {a : ℂ}
  {v du : ℂ}
  {j k : Fin 3}
-- given
  (h0 : ℤ)
  (hdu : du ≠ 0)
  (hjk : j ≠ k) :
-- imply
  Disjoint (hexKOneBaseTurns R a h0 v du hdu j) (hexKOneBaseTurns R a h0 v du hdu k) := by
-- proof
  apply StatMech.Universality.hexKOneBaseTurns_disjoint R a h0 v du hdu hjk

/--
[hexPBase_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean)
-/
@[path]
private lemma hexPBase_valid_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {R : HexFiniteRegion}
  {a : ℂ}
  {v du : ℂ}
  {n : ℕ}
-- given
  (h0 : ℤ)
  (hdu : du ≠ 0)
  (hn : n ∈ hexPBaseIndices R a h0 v du hdu) :
-- imply
  (ofTurns a h0 (hexDecodedTurns n)).IsLegalSAW ∧ (ofTurns a h0 (hexDecodedTurns n)).StaysIn R.inRegion ∧ (ofTurns a h0 (hexDecodedTurns n)).EndsAt (v + du) := by
-- proof
  apply StatMech.Universality.hexPBase_valid R a h0 v du hdu n hn

/--
[hexPBase_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean)
-/
@[path]
private lemma hexPBase_injective_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {R : HexFiniteRegion}
  {a : ℂ}
  {v du : ℂ}
-- given
  (h0 : ℤ)
  (hdu : du ≠ 0) :
-- imply
  ∀ n₁ n₂ : hexPBaseIndices R a h0 v du hdu, hexDecodedTurns n₁ = hexDecodedTurns n₂ → n₁ = n₂ := by
-- proof
  apply StatMech.Universality.hexPBase_injective R a h0 v du hdu

/--
[hexPBase_classify](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean)
-/
@[path]
private lemma hexPBase_classify_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {R : HexFiniteRegion}
  {a : ℂ}
  {v du : ℂ}
-- given
  (h0 : ℤ)
  (hdu : du ≠ 0) :
-- imply
  ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du), (ofTurns a h0 ts).EndsAt (v + du) → ∃ n : ℕ, n ∈ hexPBaseIndices R a h0 v du hdu ∧ hexDecodedTurns n = ts := by
-- proof
  apply StatMech.Universality.hexPBase_classify R a h0 v du hdu

/--
[no_fixedP_classification_of_nil_at_q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean)
-/
@[path]
private lemma no_fixedP_classification_of_nil_at_q_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
-- given
  (hsupp : ([] : List ℤ) ∈ Function.support (combinedSummand region a h0 v du))
  (hend : (ofTurns a h0 ([] : List ℤ)).EndsAt (v + hexOmega * du)) :
-- imply
  ¬ Nonempty (HexSawClassification region a h0 v du) := by
-- proof
  apply StatMech.Universality.no_fixedP_classification_of_nil_at_q hsupp hend


-- created on 2026-10-23
