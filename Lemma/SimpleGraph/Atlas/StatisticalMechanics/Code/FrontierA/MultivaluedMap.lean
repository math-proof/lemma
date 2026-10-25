import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.MultivaluedMap
open Finset StatMech StatMech.FrontierA


/--
[multivaluedMap_source_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MultivaluedMap.lean)
-/
@[path]
private lemma multivaluedMap_source_bound_eq
  [Fintype T]
  [DecidableRel R]
  {K : ℕ}
  {s : S}
-- given
  (R : S → T → Prop)
  (epsilon : ℝ≥0∞)
  (sourceWeight : S → ℝ≥0∞)
  (targetWeight : T → ℝ≥0∞)
  (hdegree : ∀ s, K ≤ (Finset.univ.filter (R s)).card)
  (hweight : ∀ s t, R s t → epsilon * sourceWeight s ≤ targetWeight t) :
-- imply
  epsilon * K * sourceWeight s ≤ ∑ t ∈ Finset.univ.filter (R s), targetWeight t := by
-- proof
  apply StatMech.FrontierA.multivaluedMap_source_bound R epsilon K sourceWeight targetWeight hdegree hweight s

/--
[multivaluedMap_weight_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MultivaluedMap.lean)
-/
@[path]
private lemma multivaluedMap_weight_bound_eq
  [Fintype T]
  [Fintype S]
  [DecidableRel R]
  {K L : ℕ}
-- given
  (R : S → T → Prop)
  (epsilon : ℝ≥0∞)
  (sourceWeight : S → ℝ≥0∞)
  (targetWeight : T → ℝ≥0∞)
  (hdegree : ∀ s, K ≤ (Finset.univ.filter (R s)).card)
  (hmultiplicity : ∀ t, (Finset.univ.filter (fun s => R s t)).card ≤ L)
  (hweight : ∀ s t, R s t → epsilon * sourceWeight s ≤ targetWeight t) :
-- imply
  epsilon * K * (∑ s, sourceWeight s) ≤ L * (∑ t, targetWeight t) := by
-- proof
  apply StatMech.FrontierA.multivaluedMap_weight_bound R epsilon K L sourceWeight targetWeight hdegree hmultiplicity hweight

/--
[multivaluedMap_probability_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MultivaluedMap.lean)
-/
@[path]
private lemma multivaluedMap_probability_bound_eq
  [Fintype T]
  [Fintype S]
  [DecidableRel R]
  {K L : ℕ}
-- given
  (R : S → T → Prop)
  (epsilon : ℝ≥0∞)
  (sourceWeight : S → ℝ≥0∞)
  (targetWeight : T → ℝ≥0∞)
  (hdegree : ∀ s, K ≤ (Finset.univ.filter (R s)).card)
  (hmultiplicity : ∀ t, (Finset.univ.filter (fun s => R s t)).card ≤ L)
  (hweight : ∀ s t, R s t → epsilon * sourceWeight s ≤ targetWeight t)
  (htarget : (∑ t, targetWeight t) ≤ 1) :
-- imply
  epsilon * K * (∑ s, sourceWeight s) ≤ L := by
-- proof
  apply StatMech.FrontierA.multivaluedMap_probability_bound R epsilon K L sourceWeight targetWeight hdegree hmultiplicity hweight htarget


-- created on 2026-10-23
