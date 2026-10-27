import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.StatisticalMechanics.Code.Universality.HexVertexEnum.Part5
open StatMech StatMech.Universality StatMech.Universality.HexVertexEnumeration


/--
[hexPhase_eq_lambda_zpow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean)
-/
@[path]
private lemma hexPhase_eq_lambda_zpow_eq
  {w : HexWalk} :
-- imply
  Complex.exp (-Complex.I * ((5/8 : ℝ) : ℂ) * ((w.turning : ℝ) : ℂ)) = hexLambda ^ (w.turnCount) := by
-- proof
  apply StatMech.Universality.hexPhase_eq_lambda_zpow w

/--
[hexContribution_eq_paraf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean)
-/
@[path]
private lemma hexContribution_eq_paraf_eq
  {a : ℂ}
  {z v : ℂ}
  {ts : List ℤ}
-- given
  (region : ℂ → Prop)
  (h0 : ℤ)
  (hcond : (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn region ∧ (ofTurns a h0 ts).EndsAt z) :
-- imply
  (z - v) * parafSummand region a h0 z (5/8) hexChi ts = hexContribution (z - v) ((ofTurns a h0 ts).turnCount) ((ofTurns a h0 ts).numVertices) := by
-- proof
  apply StatMech.Universality.hexContribution_eq_paraf region a h0 z v ts hcond

/--
[numVertices_concat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean)
-/
@[path]
private lemma numVertices_concat_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 t : ℤ) :
-- imply
  (ofTurns a h0 (ts ++ [t])).numVertices = (ofTurns a h0 ts).numVertices + 1 := by
-- proof
  apply StatMech.Universality.numVertices_concat a h0 t ts

/--
[turnCount_concat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean)
-/
@[path]
private lemma turnCount_concat_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 t : ℤ) :
-- imply
  (ofTurns a h0 (ts ++ [t])).turnCount = (ofTurns a h0 ts).turnCount + t := by
-- proof
  apply StatMech.Universality.turnCount_concat a h0 t ts

/--
[turnCount_append_block](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean)
-/
@[path]
private lemma turnCount_append_block_eq
  {a : ℂ}
  {base block : List ℤ}
-- given
  (h0 : ℤ) :
-- imply
  (ofTurns a h0 (base ++ block)).turnCount = (ofTurns a h0 base).turnCount + block.sum := by
-- proof
  apply StatMech.Universality.turnCount_append_block a h0 base block

/--
[hexUnit_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean)
-/
@[path]
private lemma hexUnit_add_two_eq
-- given
  (h : ℤ) :
-- imply
  hexUnit (h + 2) = hexOmega * hexUnit h := by
-- proof
  apply StatMech.Universality.hexUnit_add_two h

/--
[hexUnit_add_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean)
-/
@[path]
private lemma hexUnit_add_four_eq
-- given
  (h : ℤ) :
-- imply
  hexUnit (h + 4) = hexOmega ^ 2 * hexUnit h := by
-- proof
  apply StatMech.Universality.hexUnit_add_four h

/--
[genuine_triplet_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean)
-/
@[path]
private lemma genuine_triplet_zero_eq
  {a : ℂ}
  {v du : ℂ}
  {ts : List ℤ}
-- given
  (region : ℂ → Prop)
  (h0 : ℤ)
  (hp : (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn region ∧ (ofTurns a h0 ts).EndsAt (v + du))
  (hq : (ofTurns a h0 (ts ++ [-1])).IsLegalSAW ∧ (ofTurns a h0 (ts ++ [-1])).StaysIn region ∧ (ofTurns a h0 (ts ++ [-1])).EndsAt (v + hexOmega * du))
  (hr : (ofTurns a h0 (ts ++ [1])).IsLegalSAW ∧ (ofTurns a h0 (ts ++ [1])).StaysIn region ∧ (ofTurns a h0 (ts ++ [1])).EndsAt (v + hexOmega ^ 2 * du)) :
-- imply
  ((v + du) - v) * parafSummand region a h0 (v + du) (5/8) hexChi ts + ((v + hexOmega * du) - v) * parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi (ts ++ [-1]) + ((v + hexOmega ^ 2 * du) - v) * parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi (ts ++ [1]) = 0 := by
-- proof
  apply StatMech.Universality.genuine_triplet_zero region a h0 v du ts hp hq hr

/--
[genuine_pair_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean)
-/
@[path]
private lemma genuine_pair_zero_eq
  {a : ℂ}
  {v du : ℂ}
  {base Lq Lr : List ℤ}
-- given
  (region : ℂ → Prop)
  (h0 : ℤ)
  (hLqsum : Lq.sum = -4)
  (hLrsum : Lr.sum = 4)
  (hlen : Lq.length = Lr.length)
  (hq : (ofTurns a h0 (base ++ Lq)).IsLegalSAW ∧ (ofTurns a h0 (base ++ Lq)).StaysIn region ∧ (ofTurns a h0 (base ++ Lq)).EndsAt (v + hexOmega * du))
  (hr : (ofTurns a h0 (base ++ Lr)).IsLegalSAW ∧ (ofTurns a h0 (base ++ Lr)).StaysIn region ∧ (ofTurns a h0 (base ++ Lr)).EndsAt (v + hexOmega ^ 2 * du)) :
-- imply
  ((v + hexOmega * du) - v) * parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi (base ++ Lq) + ((v + hexOmega ^ 2 * du) - v) * parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi (base ++ Lr) = 0 := by
-- proof
  apply StatMech.Universality.genuine_pair_zero region a h0 v du base Lq Lr hLqsum hLrsum hlen hq hr

/--
[loopReverse_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean)
-/
@[path]
private lemma loopReverse_sum_eq
  {L : List ℤ} :
-- imply
  (loopReverse L).sum = - L.sum := by
-- proof
  apply StatMech.Universality.loopReverse_sum L

/--
[loopReverse_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean)
-/
@[path]
private lemma loopReverse_length_eq
  {L : List ℤ} :
-- imply
  (loopReverse L).length = L.length := by
-- proof
  apply StatMech.Universality.loopReverse_length L

/--
[loopReverse_legal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean)
-/
@[path]
private lemma loopReverse_legal_eq
  {L : List ℤ}
-- given
  (hL : ∀ t ∈ L, t = 1 ∨ t = -1) :
-- imply
  ∀ t ∈ loopReverse L, t = 1 ∨ t = -1 := by
-- proof
  apply StatMech.Universality.loopReverse_legal L hL

/--
[loopReverse_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean)
-/
@[path]
private lemma loopReverse_involutive_eq
  {L : List ℤ} :
-- imply
  loopReverse (loopReverse L) = L := by
-- proof
  apply StatMech.Universality.loopReverse_involutive L

/--
[genuine_pair_zero_via_reversal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean)
-/
@[path]
private lemma genuine_pair_zero_via_reversal_eq
  {a : ℂ}
  {v du : ℂ}
  {base Lq : List ℤ}
-- given
  (region : ℂ → Prop)
  (h0 : ℤ)
  (hLqsum : Lq.sum = -4)
  (hq : (ofTurns a h0 (base ++ Lq)).IsLegalSAW ∧ (ofTurns a h0 (base ++ Lq)).StaysIn region ∧ (ofTurns a h0 (base ++ Lq)).EndsAt (v + hexOmega * du))
  (hr : (ofTurns a h0 (base ++ loopReverse Lq)).IsLegalSAW ∧ (ofTurns a h0 (base ++ loopReverse Lq)).StaysIn region ∧ (ofTurns a h0 (base ++ loopReverse Lq)).EndsAt (v + hexOmega ^ 2 * du)) :
-- imply
  ((v + hexOmega * du) - v) * parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi (base ++ Lq) + ((v + hexOmega ^ 2 * du) - v) * parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi (base ++ loopReverse Lq) = 0 := by
-- proof
  apply StatMech.Universality.genuine_pair_zero_via_reversal region a h0 v du base Lq hLqsum hq hr

/--
[hexOmega_primRoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean)
-/
@[path]
private lemma hexOmega_primRoot_eq :
-- imply
  IsPrimitiveRoot hexOmega 3 := by
-- proof
  apply StatMech.Universality.hexOmega_primRoot

/--
[hexOmega_ne_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean)
-/
@[path]
private lemma hexOmega_ne_one_eq :
-- imply
  hexOmega ≠ 1 := by
-- proof
  apply StatMech.Universality.hexOmega_ne_one

/--
[hexOmega_sq_ne_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean)
-/
@[path]
private lemma hexOmega_sq_ne_one_eq :
-- imply
  hexOmega ^ 2 ≠ 1 := by
-- proof
  apply StatMech.Universality.hexOmega_sq_ne_one

/--
[hexOmega_ne_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean)
-/
@[path]
private lemma hexOmega_ne_sq_eq :
-- imply
  hexOmega ≠ hexOmega ^ 2 := by
-- proof
  apply StatMech.Universality.hexOmega_ne_sq

/--
[hexMid_p_ne_q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean)
-/
@[path]
private lemma hexMid_p_ne_q_eq
  {v du : ℂ}
-- given
  (hdu : du ≠ 0) :
-- imply
  v + du ≠ v + hexOmega * du := by
-- proof
  apply StatMech.Universality.hexMid_p_ne_q hdu

/--
[hexMid_p_ne_r](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean)
-/
@[path]
private lemma hexMid_p_ne_r_eq
  {v du : ℂ}
-- given
  (hdu : du ≠ 0) :
-- imply
  v + du ≠ v + hexOmega ^ 2 * du := by
-- proof
  apply StatMech.Universality.hexMid_p_ne_r hdu

/--
[hexMid_q_ne_r](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean)
-/
@[path]
private lemma hexMid_q_ne_r_eq
  {v du : ℂ}
-- given
  (hdu : du ≠ 0) :
-- imply
  v + hexOmega * du ≠ v + hexOmega ^ 2 * du := by
-- proof
  apply StatMech.Universality.hexMid_q_ne_r hdu

/--
[parafSummand_eq_zero_of_not_endsAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean)
-/
@[path]
private lemma parafSummand_eq_zero_of_not_endsAt_eq
  {a : ℂ}
  {z : ℂ}
  {σ x : ℝ}
  {ts : List ℤ}
-- given
  (region : ℂ → Prop)
  (h0 : ℤ)
  (hne : ¬ (ofTurns a h0 ts).EndsAt z) :
-- imply
  parafSummand region a h0 z σ x ts = 0 := by
-- proof
  apply StatMech.Universality.parafSummand_eq_zero_of_not_endsAt region a h0 z σ x ts hne

/--
[combinedSummand_at_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean)
-/
@[path]
private lemma combinedSummand_at_p_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {ts : List ℤ}
-- given
  (hdu : du ≠ 0)
  (hend : (ofTurns a h0 ts).EndsAt (v + du)) :
-- imply
  combinedSummand region a h0 v du ts = ((v + du) - v) * parafSummand region a h0 (v + du) (5/8) hexChi ts := by
-- proof
  apply StatMech.Universality.combinedSummand_at_p hdu hend

/--
[combinedSummand_at_q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean)
-/
@[path]
private lemma combinedSummand_at_q_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {ts : List ℤ}
-- given
  (hdu : du ≠ 0)
  (hend : (ofTurns a h0 ts).EndsAt (v + hexOmega * du)) :
-- imply
  combinedSummand region a h0 v du ts = ((v + hexOmega * du) - v) * parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi ts := by
-- proof
  apply StatMech.Universality.combinedSummand_at_q hdu hend

/--
[combinedSummand_at_r](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean)
-/
@[path]
private lemma combinedSummand_at_r_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {ts : List ℤ}
-- given
  (hdu : du ≠ 0)
  (hend : (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du)) :
-- imply
  combinedSummand region a h0 v du ts = ((v + hexOmega ^ 2 * du) - v) * parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts := by
-- proof
  apply StatMech.Universality.combinedSummand_at_r hdu hend

/--
[vertexSum_eq_tsum_combinedSummand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean)
-/
@[path]
private lemma vertexSum_eq_tsum_combinedSummand_eq
  {a : ℂ}
  {v du : ℂ}
-- given
  (region : ℂ → Prop)
  (h0 : ℤ)
  (hp : Summable fun ts => parafSummand region a h0 (v + du) (5/8) hexChi ts)
  (hq : Summable fun ts => parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi ts)
  (hr : Summable fun ts => parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts) :
-- imply
  ((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi + ((v + hexOmega ^ 2 * du) - v) * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = ∑' ts, combinedSummand region a h0 v du ts := by
-- proof
  apply StatMech.Universality.vertexSum_eq_tsum_combinedSummand region a h0 v du hp hq hr

/--
[relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean)
-/
@[path]
private lemma relation_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {E : HexVertexEnumeration region a h0 v du} :
-- imply
  ((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi + ((v + hexOmega ^ 2 * du) - v) * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 := by
-- proof
  apply StatMech.Universality.HexVertexEnumeration.relation E

/--
[vertexSum_toVertexWalkData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean)
-/
@[path]
private lemma vertexSum_toVertexWalkData_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {E : HexVertexEnumeration region a h0 v du} :
-- imply
  ((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi + ((v + hexOmega ^ 2 * du) - v) * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = (toVertexWalkData E).vertexSum := by
-- proof
  apply StatMech.Universality.HexVertexEnumeration.vertexSum_toVertexWalkData E

/--
[relation_via_vertexWalkData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean)
-/
@[path]
private lemma relation_via_vertexWalkData_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {E : HexVertexEnumeration region a h0 v du} :
-- imply
  ((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi + ((v + hexOmega ^ 2 * du) - v) * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 := by
-- proof
  apply StatMech.Universality.HexVertexEnumeration.relation_via_vertexWalkData E

/--
[tsum_combinedSummand_slot_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean)
-/
@[path]
private lemma tsum_combinedSummand_slot_eq_zero_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {E : HexVertexEnumeration region a h0 v du}
-- given
  (hdu : du ≠ 0) :
-- imply
  ∑' slot, combinedSummand region a h0 v du (slotTurns E slot) = 0 := by
-- proof
  apply StatMech.Universality.HexVertexEnumeration.tsum_combinedSummand_slot_eq_zero E hdu

/--
[relation_of_bijection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean)
-/
@[path]
private lemma relation_of_bijection_eq
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
  (hinj : Function.Injective fun x : Function.support (combinedSummand region a h0 v du ∘ slotTurns E) => slotTurns E x.1)
  (hsub : Function.support (combinedSummand region a h0 v du) ⊆ Set.range fun x : Function.support (combinedSummand region a h0 v du ∘ slotTurns E) => slotTurns E x.1) :
-- imply
  ((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi + ((v + hexOmega ^ 2 * du) - v) * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 := by
-- proof
  apply StatMech.Universality.HexVertexEnumeration.relation_of_bijection E hdu hp hq hr hinj hsub


-- created on 2026-10-23
