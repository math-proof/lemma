import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexVertexBijection
open StatMech StatMech.Universality StatMech.Universality.HexVertexBijection


/--
[hinj_of_leftInverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBijection.lean)
-/
@[path]
private lemma hinj_of_leftInverse_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {E : HexVertexEnumeration region a h0 v du}
  {cls : List ℤ → SlotType E}
-- given
  (hleft : ∀ slot ∈ Function.support (combinedSummand region a h0 v du ∘ E.slotTurns), cls (E.slotTurns slot) = slot) :
-- imply
  Function.Injective fun x : Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) => E.slotTurns x.1 := by
-- proof
  apply StatMech.Universality.hinj_of_leftInverse E cls hleft

/--
[hsub_of_rightInverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBijection.lean)
-/
@[path]
private lemma hsub_of_rightInverse_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {E : HexVertexEnumeration region a h0 v du}
  {cls : List ℤ → SlotType E}
-- given
  (hright : ∀ ts ∈ Function.support (combinedSummand region a h0 v du), E.slotTurns (cls ts) = ts) :
-- imply
  Function.support (combinedSummand region a h0 v du) ⊆ Set.range fun x : Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) => E.slotTurns x.1 := by
-- proof
  apply StatMech.Universality.hsub_of_rightInverse E cls hright

/--
[hinj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBijection.lean)
-/
@[path]
private lemma hinj_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {B : HexVertexBijection region a h0 v du} :
-- imply
  Function.Injective fun x : Function.support (combinedSummand region a h0 v du ∘ B.enum.slotTurns) => B.enum.slotTurns x.1 := by
-- proof
  apply StatMech.Universality.HexVertexBijection.hinj B

/--
[hsub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBijection.lean)
-/
@[path]
private lemma hsub_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {B : HexVertexBijection region a h0 v du} :
-- imply
  Function.support (combinedSummand region a h0 v du) ⊆ Set.range fun x : Function.support (combinedSummand region a h0 v du ∘ B.enum.slotTurns) => B.enum.slotTurns x.1 := by
-- proof
  apply StatMech.Universality.HexVertexBijection.hsub B

/--
[relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBijection.lean)
-/
@[path]
private lemma relation_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {B : HexVertexBijection region a h0 v du}
  {B : HexVertexBijection region a h0 v du}
-- given
  (hdu : du ≠ 0)
  (hp : Summable fun ts => parafSummand region a h0 (v + du) (5/8) hexChi ts)
  (hq : Summable fun ts => parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi ts)
  (hr : Summable fun ts => parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts) :
-- imply
  ((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi + ((v + hexOmega ^ 2 * du) - v) * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 := by
-- proof
  apply StatMech.Universality.HexVertexBijection.relation B B hdu hp hq hr

/--
[slot_endsAt_label](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBijection.lean)
-/
@[path]
private lemma slot_endsAt_label_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {E : HexVertexEnumeration region a h0 v du}
  {slot : (E.pairs × Bool) ⊕ (E.triplets × Fin 3)} :
-- imply
  (ofTurns a h0 (E.slotTurns slot)).EndsAt (labelMid v du (slotLabel slot)) := by
-- proof
  apply StatMech.Universality.slot_endsAt_label E slot

/--
[labelMid_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBijection.lean)
-/
@[path]
private lemma labelMid_injective_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
-- given
  (hdu : du ≠ 0) :
-- imply
  Function.Injective (labelMid v du) := by
-- proof
  apply StatMech.Universality.labelMid_injective hdu

/--
[slotLabel_eq_of_slotTurns_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBijection.lean)
-/
@[path]
private lemma slotLabel_eq_of_slotTurns_eq_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {E : HexVertexEnumeration region a h0 v du}
  {s1 s2 : (E.pairs × Bool) ⊕ (E.triplets × Fin 3)}
-- given
  (hdu : du ≠ 0)
  (h : E.slotTurns s1 = E.slotTurns s2) :
-- imply
  slotLabel s1 = slotLabel s2 := by
-- proof
  apply StatMech.Universality.slotLabel_eq_of_slotTurns_eq E hdu s1 s2 h

/--
[support_endsAt_threeMid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBijection.lean)
-/
@[path]
private lemma support_endsAt_threeMid_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {ts : List ℤ}
-- given
  (h : ts ∈ Function.support (combinedSummand region a h0 v du)) :
-- imply
  (ofTurns a h0 ts).EndsAt (v + du) ∨ (ofTurns a h0 ts).EndsAt (v + hexOmega * du) ∨ (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) := by
-- proof
  apply StatMech.Universality.support_endsAt_threeMid ts h

/--
[support_isLegalSAW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBijection.lean)
-/
@[path]
private lemma support_isLegalSAW_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {ts : List ℤ}
-- given
  (h : ts ∈ Function.support (combinedSummand region a h0 v du))
  (hp : (ofTurns a h0 ts).EndsAt (v + du))
  (hdu : du ≠ 0) :
-- imply
  (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn region := by
-- proof
  apply StatMech.Universality.support_isLegalSAW ts h hp hdu

/--
[hinj_of_perLabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBijection.lean)
-/
@[path]
private lemma hinj_of_perLabel_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {E : HexVertexEnumeration region a h0 v du}
-- given
  (hdu : du ≠ 0)
  (hlabel : ∀ s1 s2 : (E.pairs × Bool) ⊕ (E.triplets × Fin 3), slotLabel s1 = slotLabel s2 → E.slotTurns s1 = E.slotTurns s2 → s1 = s2) :
-- imply
  Function.Injective fun x : Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) => E.slotTurns x.1 := by
-- proof
  apply StatMech.Universality.hinj_of_perLabel E hdu hlabel

/--
[hinj_of_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBijection.lean)
-/
@[path]
private lemma hinj_of_injective_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {E : HexVertexEnumeration region a h0 v du}
-- given
  (hsti : Function.Injective E.slotTurns) :
-- imply
  Function.Injective fun x : Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) => E.slotTurns x.1 := by
-- proof
  apply StatMech.Universality.hinj_of_injective E hsti

/--
[hlabel_tripletOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBijection.lean)
-/
@[path]
private lemma hlabel_tripletOnly_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {E : HexVertexEnumeration region a h0 v du}
-- given
  (hnopairs : E.pairs = ∅)
  (htinj : ∀ T1 T2 : E.triplets, E.tripBase T1 = E.tripBase T2 → T1 = T2) :
-- imply
  ∀ s1 s2 : (E.pairs × Bool) ⊕ (E.triplets × Fin 3), slotLabel s1 = slotLabel s2 → E.slotTurns s1 = E.slotTurns s2 → s1 = s2 := by
-- proof
  apply StatMech.Universality.hlabel_tripletOnly E hnopairs htinj

/--
[hinj_tripletOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBijection.lean)
-/
@[path]
private lemma hinj_tripletOnly_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {E : HexVertexEnumeration region a h0 v du}
-- given
  (hdu : du ≠ 0)
  (hnopairs : E.pairs = ∅)
  (htinj : ∀ T1 T2 : E.triplets, E.tripBase T1 = E.tripBase T2 → T1 = T2) :
-- imply
  Function.Injective fun x : Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) => E.slotTurns x.1 := by
-- proof
  apply StatMech.Universality.hinj_tripletOnly E hdu hnopairs htinj

/--
[hlabel_pairOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBijection.lean)
-/
@[path]
private lemma hlabel_pairOnly_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {E : HexVertexEnumeration region a h0 v du}
-- given
  (hnotrip : E.triplets = ∅)
  (hqinj : ∀ P1 P2 : E.pairs, E.pairBase P1 ++ E.pairLq P1 = E.pairBase P2 ++ E.pairLq P2 → P1 = P2)
  (hrinj : ∀ P1 P2 : E.pairs, E.pairBase P1 ++ E.pairLr P1 = E.pairBase P2 ++ E.pairLr P2 → P1 = P2) :
-- imply
  ∀ s1 s2 : (E.pairs × Bool) ⊕ (E.triplets × Fin 3), slotLabel s1 = slotLabel s2 → E.slotTurns s1 = E.slotTurns s2 → s1 = s2 := by
-- proof
  apply StatMech.Universality.hlabel_pairOnly E hnotrip hqinj hrinj

/--
[hinj_pairOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBijection.lean)
-/
@[path]
private lemma hinj_pairOnly_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {E : HexVertexEnumeration region a h0 v du}
-- given
  (hdu : du ≠ 0)
  (hnotrip : E.triplets = ∅)
  (hqinj : ∀ P1 P2 : E.pairs, E.pairBase P1 ++ E.pairLq P1 = E.pairBase P2 ++ E.pairLq P2 → P1 = P2)
  (hrinj : ∀ P1 P2 : E.pairs, E.pairBase P1 ++ E.pairLr P1 = E.pairBase P2 ++ E.pairLr P2 → P1 = P2) :
-- imply
  Function.Injective fun x : Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) => E.slotTurns x.1 := by
-- proof
  apply StatMech.Universality.hinj_pairOnly E hdu hnotrip hqinj hrinj

/--
[hlabel_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBijection.lean)
-/
@[path]
private lemma hlabel_general_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {E : HexVertexEnumeration region a h0 v du}
-- given
  (htinj : ∀ T1 T2 : E.triplets, E.tripBase T1 = E.tripBase T2 → T1 = T2)
  (hqinj : ∀ P1 P2 : E.pairs, E.pairBase P1 ++ E.pairLq P1 = E.pairBase P2 ++ E.pairLq P2 → P1 = P2)
  (hrinj : ∀ P1 P2 : E.pairs, E.pairBase P1 ++ E.pairLr P1 = E.pairBase P2 ++ E.pairLr P2 → P1 = P2)
  (hqcross : ∀ (P : E.pairs) (T : E.triplets), E.pairBase P ++ E.pairLq P ≠ E.tripBase T ++ [-1])
  (hrcross : ∀ (P : E.pairs) (T : E.triplets), E.pairBase P ++ E.pairLr P ≠ E.tripBase T ++ [1]) :
-- imply
  ∀ s1 s2 : (E.pairs × Bool) ⊕ (E.triplets × Fin 3), slotLabel s1 = slotLabel s2 → E.slotTurns s1 = E.slotTurns s2 → s1 = s2 := by
-- proof
  apply StatMech.Universality.hlabel_general E htinj hqinj hrinj hqcross hrcross

/--
[hinj_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBijection.lean)
-/
@[path]
private lemma hinj_general_eq
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
  (hqcross : ∀ (P : E.pairs) (T : E.triplets), E.pairBase P ++ E.pairLq P ≠ E.tripBase T ++ [-1])
  (hrcross : ∀ (P : E.pairs) (T : E.triplets), E.pairBase P ++ E.pairLr P ≠ E.tripBase T ++ [1]) :
-- imply
  Function.Injective fun x : Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) => E.slotTurns x.1 := by
-- proof
  apply StatMech.Universality.hinj_general E hdu htinj hqinj hrinj hqcross hrcross

/--
[hsub_of_coverage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBijection.lean)
-/
@[path]
private lemma hsub_of_coverage_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {E : HexVertexEnumeration region a h0 v du}
-- given
  (covp : ∀ ts ∈ Function.support (combinedSummand region a h0 v du), (ofTurns a h0 ts).EndsAt (v + du) → ∃ slot : SlotType E, E.slotTurns slot = ts)
  (covq : ∀ ts ∈ Function.support (combinedSummand region a h0 v du), (ofTurns a h0 ts).EndsAt (v + hexOmega * du) → ∃ slot : SlotType E, E.slotTurns slot = ts)
  (covr : ∀ ts ∈ Function.support (combinedSummand region a h0 v du), (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) → ∃ slot : SlotType E, E.slotTurns slot = ts) :
-- imply
  Function.support (combinedSummand region a h0 v du) ⊆ Set.range fun x : Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) => E.slotTurns x.1 := by
-- proof
  apply StatMech.Universality.hsub_of_coverage E covp covq covr

/--
[relation_of_partitionFacts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBijection.lean)
-/
@[path]
private lemma relation_of_partitionFacts_eq
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
  (hqcross : ∀ (P : E.pairs) (T : E.triplets), E.pairBase P ++ E.pairLq P ≠ E.tripBase T ++ [-1])
  (hrcross : ∀ (P : E.pairs) (T : E.triplets), E.pairBase P ++ E.pairLr P ≠ E.tripBase T ++ [1])
  (covp : ∀ ts ∈ Function.support (combinedSummand region a h0 v du), (ofTurns a h0 ts).EndsAt (v + du) → ∃ slot : SlotType E, E.slotTurns slot = ts)
  (covq : ∀ ts ∈ Function.support (combinedSummand region a h0 v du), (ofTurns a h0 ts).EndsAt (v + hexOmega * du) → ∃ slot : SlotType E, E.slotTurns slot = ts)
  (covr : ∀ ts ∈ Function.support (combinedSummand region a h0 v du), (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) → ∃ slot : SlotType E, E.slotTurns slot = ts) :
-- imply
  ((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi + ((v + hexOmega ^ 2 * du) - v) * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 := by
-- proof
  apply StatMech.Universality.relation_of_partitionFacts E hdu hp hq hr htinj hqinj hrinj hqcross hrcross covp covq covr

/--
[parafSummand_emptyRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBijection.lean)
-/
@[path]
private lemma parafSummand_emptyRegion_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {a : ℂ}
  {z : ℂ}
  {σ x : ℝ}
  {ts : List ℤ}
-- given
  (h0 : ℤ) :
-- imply
  parafSummand (fun _ => False) a h0 z σ x ts = 0 := by
-- proof
  apply StatMech.Universality.parafSummand_emptyRegion a h0 z σ x ts

/--
[parafObservable_emptyRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBijection.lean)
-/
@[path]
private lemma parafObservable_emptyRegion_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {a : ℂ}
  {z : ℂ}
  {σ x : ℝ}
-- given
  (h0 : ℤ) :
-- imply
  parafObservable (fun _ => False) a h0 z σ x = 0 := by
-- proof
  apply StatMech.Universality.parafObservable_emptyRegion a h0 z σ x

/--
[combinedSummand_emptyRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBijection.lean)
-/
@[path]
private lemma combinedSummand_emptyRegion_eq
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
  combinedSummand (fun _ => False) a h0 v du ts = 0 := by
-- proof
  apply StatMech.Universality.combinedSummand_emptyRegion a h0 v du ts

/--
[summable_emptyRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBijection.lean)
-/
@[path]
private lemma summable_emptyRegion_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {a : ℂ}
  {z : ℂ}
  {σ x : ℝ}
-- given
  (h0 : ℤ) :
-- imply
  Summable fun ts => parafSummand (fun _ => False) a h0 z σ x ts := by
-- proof
  apply StatMech.Universality.summable_emptyRegion a h0 z σ x

/--
[relation_emptyRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBijection.lean)
-/
@[path]
private lemma relation_emptyRegion_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {a : ℂ}
  {v du : ℂ}
-- given
  (h0 : ℤ)
  (hdu : du ≠ 0) :
-- imply
  ((v + du) - v) * parafObservable (fun _ => False) a h0 (v + du) (5/8) hexChi + ((v + hexOmega * du) - v) * parafObservable (fun _ => False) a h0 (v + hexOmega * du) (5/8) hexChi + ((v + hexOmega ^ 2 * du) - v) * parafObservable (fun _ => False) a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 := by
-- proof
  apply StatMech.Universality.relation_emptyRegion a h0 v du hdu


-- created on 2026-10-23
