import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexVertexClassification.Part3
open StatMech StatMech.Universality StatMech.Universality.HexSawClassification


/--
[hexClass_endsAt_passesThrough](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexClassification.lean)
-/
@[path]
private lemma hexClass_endsAt_passesThrough_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {ts : List ℤ}
  {z : ℂ}
-- given
  (h : (ofTurns a h0 ts).EndsAt z) :
-- imply
  PassesThrough a h0 ts z := by
-- proof
  apply StatMech.Universality.hexClass_endsAt_passesThrough ts z h

/--
[hexClass_specialMidCount_three_of_passes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexClassification.lean)
-/
@[path]
private lemma hexClass_specialMidCount_three_of_passes_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {ts : List ℤ}
-- given
  (hp : PassesThrough a h0 ts (v + du))
  (hq : PassesThrough a h0 ts (v + hexOmega * du))
  (hr : PassesThrough a h0 ts (v + hexOmega ^ 2 * du)) :
-- imply
  specialMidCount a h0 v du ts = 3 := by
-- proof
  apply StatMech.Universality.hexClass_specialMidCount_three_of_passes ts hp hq hr

/--
[toEnum_pairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexClassification.lean)
-/
@[path]
private lemma toEnum_pairs_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {C : HexSawClassification region a h0 v du} :
-- imply
  C.toEnum.pairs = C.pairs := by
-- proof
  apply StatMech.Universality.HexSawClassification.toEnum_pairs C

/--
[toEnum_triplets](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexClassification.lean)
-/
@[path]
private lemma toEnum_triplets_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {C : HexSawClassification region a h0 v du} :
-- imply
  C.toEnum.triplets = C.triplets := by
-- proof
  apply StatMech.Universality.HexSawClassification.toEnum_triplets C

/--
[toEnum_pairBase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexClassification.lean)
-/
@[path]
private lemma toEnum_pairBase_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {C : HexSawClassification region a h0 v du} :
-- imply
  C.toEnum.pairBase = C.pairBase := by
-- proof
  apply StatMech.Universality.HexSawClassification.toEnum_pairBase C

/--
[toEnum_pairLq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexClassification.lean)
-/
@[path]
private lemma toEnum_pairLq_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {C : HexSawClassification region a h0 v du} :
-- imply
  C.toEnum.pairLq = C.pairLq := by
-- proof
  apply StatMech.Universality.HexSawClassification.toEnum_pairLq C

/--
[toEnum_pairLr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexClassification.lean)
-/
@[path]
private lemma toEnum_pairLr_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {C : HexSawClassification region a h0 v du} :
-- imply
  C.toEnum.pairLr = C.pairLr := by
-- proof
  apply StatMech.Universality.HexSawClassification.toEnum_pairLr C

/--
[toEnum_tripBase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexClassification.lean)
-/
@[path]
private lemma toEnum_tripBase_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {C : HexSawClassification region a h0 v du} :
-- imply
  C.toEnum.tripBase = C.tripBase := by
-- proof
  apply StatMech.Universality.HexSawClassification.toEnum_tripBase C

/--
[hexClass_separated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexClassification.lean)
-/
@[path]
private lemma hexClass_separated_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {C : HexSawClassification region a h0 v du} :
-- imply
  HexVertexSeparated C.toEnum where pairQ_count_three := by
-- proof
  apply StatMech.Universality.hexClass_separated C

/--
[hexClass_complete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexClassification.lean)
-/
@[path]
private lemma hexClass_complete_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {C : HexSawClassification region a h0 v du} :
-- imply
  HexVertexComplete C.toEnum where complete_p := by
-- proof
  apply StatMech.Universality.hexClass_complete C

/--
[hexClass_vertex_relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexClassification.lean)
-/
@[path]
private lemma hexClass_vertex_relation_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {C : HexSawClassification region a h0 v du}
-- given
  (hdu : du ≠ 0)
  (hp : Summable fun ts => parafSummand region a h0 (v + du) (5/8) hexChi ts)
  (hq : Summable fun ts => parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi ts)
  (hr : Summable fun ts => parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts) :
-- imply
  ((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi + ((v + hexOmega ^ 2 * du) - v) * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 := by
-- proof
  apply StatMech.Universality.hexClass_vertex_relation C hdu hp hq hr

/--
[hexClass_vertex_relation_singleTriplet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexClassification.lean)
-/
@[path]
private lemma hexClass_vertex_relation_singleTriplet_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {a : ℂ}
  {v du : ℂ}
  {tb : List ℤ}
-- given
  (region : ℂ → Prop)
  (h0 : ℤ)
  (hdu : du ≠ 0)
  (hp0 : Summable fun ts => parafSummand region a h0 (v + du) (5/8) hexChi ts)
  (hq0 : Summable fun ts => parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi ts)
  (hr0 : Summable fun ts => parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts)
  (hp : (ofTurns a h0 tb).IsLegalSAW ∧ (ofTurns a h0 tb).StaysIn region ∧ (ofTurns a h0 tb).EndsAt (v + du))
  (hq : (ofTurns a h0 (tb ++ [-1])).IsLegalSAW ∧ (ofTurns a h0 (tb ++ [-1])).StaysIn region ∧ (ofTurns a h0 (tb ++ [-1])).EndsAt (v + hexOmega * du))
  (hr : (ofTurns a h0 (tb ++ [1])).IsLegalSAW ∧ (ofTurns a h0 (tb ++ [1])).StaysIn region ∧ (ofTurns a h0 (tb ++ [1])).EndsAt (v + hexOmega ^ 2 * du))
  (hQr : ¬ PassesThrough a h0 (tb ++ [-1]) (v + hexOmega ^ 2 * du))
  (hRq : ¬ PassesThrough a h0 (tb ++ [1]) (v + hexOmega * du))
  (hcp : ∀ ts ∈ Function.support (combinedSummand region a h0 v du), (ofTurns a h0 ts).EndsAt (v + du) → tb = ts)
  (hcq : ∀ ts ∈ Function.support (combinedSummand region a h0 v du), (ofTurns a h0 ts).EndsAt (v + hexOmega * du) → tb ++ [-1] = ts)
  (hcr : ∀ ts ∈ Function.support (combinedSummand region a h0 v du), (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) → tb ++ [1] = ts)
  (hreindex : (((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi + ((v + hexOmega ^ 2 * du) - v) * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi) = ((v + du) - v) * parafSummand region a h0 (v + du) (5/8) hexChi tb + ((v + hexOmega * du) - v) * parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi (tb ++ [-1]) + ((v + hexOmega ^ 2 * du) - v) * parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi (tb ++ [1])) :
-- imply
  ((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi + ((v + hexOmega ^ 2 * du) - v) * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 := by
-- proof
  apply StatMech.Universality.hexClass_vertex_relation_singleTriplet region a h0 v du tb hdu hp0 hq0 hr0 hp hq hr hQr hRq hcp hcq hcr hreindex


-- created on 2026-10-23
