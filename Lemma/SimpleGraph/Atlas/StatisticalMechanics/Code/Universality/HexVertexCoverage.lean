import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexVertexCoverage
open StatMech StatMech.Universality


/--
[hexCov_covp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexCoverage.lean)
-/
@[path]
private lemma hexCov_covp_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {E : HexVertexEnumeration region a h0 v du}
-- given
  (hC : HexVertexComplete E) :
-- imply
  ∀ ts ∈ Function.support (combinedSummand region a h0 v du), (ofTurns a h0 ts).EndsAt (v + du) → ∃ slot : SlotType E, E.slotTurns slot = ts := by
-- proof
  apply StatMech.Universality.hexCov_covp E hC

/--
[hexCov_covq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexCoverage.lean)
-/
@[path]
private lemma hexCov_covq_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {E : HexVertexEnumeration region a h0 v du}
-- given
  (hC : HexVertexComplete E) :
-- imply
  ∀ ts ∈ Function.support (combinedSummand region a h0 v du), (ofTurns a h0 ts).EndsAt (v + hexOmega * du) → ∃ slot : SlotType E, E.slotTurns slot = ts := by
-- proof
  apply StatMech.Universality.hexCov_covq E hC

/--
[hexCov_covr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexCoverage.lean)
-/
@[path]
private lemma hexCov_covr_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {E : HexVertexEnumeration region a h0 v du}
-- given
  (hC : HexVertexComplete E) :
-- imply
  ∀ ts ∈ Function.support (combinedSummand region a h0 v du), (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) → ∃ slot : SlotType E, E.slotTurns slot = ts := by
-- proof
  apply StatMech.Universality.hexCov_covr E hC

/--
[hsub_from_coverage_proved](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexCoverage.lean)
-/
@[path]
private lemma hsub_from_coverage_proved_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {E : HexVertexEnumeration region a h0 v du}
-- given
  (hC : HexVertexComplete E) :
-- imply
  Function.support (combinedSummand region a h0 v du) ⊆ Set.range fun x : Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) => E.slotTurns x.1 := by
-- proof
  apply StatMech.Universality.hsub_from_coverage_proved E hC

/--
[relation_of_complete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexCoverage.lean)
-/
@[path]
private lemma relation_of_complete_eq
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
  (hC : HexVertexComplete E) :
-- imply
  ((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi + ((v + hexOmega ^ 2 * du) - v) * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 := by
-- proof
  apply StatMech.Universality.relation_of_complete E hdu hp hq hr htinj hqinj hrinj hqcross hrcross hC

/--
[complete_emptyRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexCoverage.lean)
-/
@[path]
private lemma complete_emptyRegion_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {a : ℂ}
  {v du : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  HexVertexComplete (emptyEnumeration a h0 v du) where complete_p := by
-- proof
  apply StatMech.Universality.complete_emptyRegion a h0 v du

/--
[relation_complete_emptyRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexCoverage.lean)
-/
@[path]
private lemma relation_complete_emptyRegion_eq
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
  apply StatMech.Universality.relation_complete_emptyRegion a h0 v du hdu


-- created on 2026-10-23
