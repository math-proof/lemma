import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexVertexBoundConcrete.Part4
open StatMech StatMech.Universality


/--
[hexVBC_vertexBound_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean)
-/
@[path]
private lemma hexVBC_vertexBound_false_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  ¬ (∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) → ∀ x ∈ W.vertices, x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) := by
-- proof
  apply StatMech.Universality.hexVBC_vertexBound_false a h0

/--
[hexVBC_vert_eq_mid_plus_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean)
-/
@[path]
private lemma hexVBC_vert_eq_mid_plus_step_eq
  {m : ℂ}
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  ∀ x ∈ verticesAux m h ts, ∃ mm ∈ midsAux m h ts, ∃ hh : ℤ, x = mm + halfStep hh := by
-- proof
  apply StatMech.Universality.hexVBC_vert_eq_mid_plus_step m h ts

/--
[hexVBC_halfStep_add6](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean)
-/
@[path]
private lemma hexVBC_halfStep_add6_eq
-- given
  (h : ℤ) :
-- imply
  halfStep (h + 6) = halfStep h := by
-- proof
  apply StatMech.Universality.hexVBC_halfStep_add6 h

/--
[hexVBC_step0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean)
-/
@[path]
private lemma hexVBC_step0_eq
-- given
  (h0 : ℤ) :
-- imply
  halfStep (h0 + 0) = (((1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
-- proof
  apply StatMech.Universality.hexVBC_step0 h0

/--
[hexVBC_step1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean)
-/
@[path]
private lemma hexVBC_step1_eq
-- given
  (h0 : ℤ) :
-- imply
  halfStep (h0 + 1) = (((1 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
-- proof
  apply StatMech.Universality.hexVBC_step1 h0

/--
[hexVBC_step2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean)
-/
@[path]
private lemma hexVBC_step2_eq
-- given
  (h0 : ℤ) :
-- imply
  halfStep (h0 + 2) = (((0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
-- proof
  apply StatMech.Universality.hexVBC_step2 h0

/--
[hexVBC_step3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean)
-/
@[path]
private lemma hexVBC_step3_eq
-- given
  (h0 : ℤ) :
-- imply
  halfStep (h0 + 3) = (((-1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
-- proof
  apply StatMech.Universality.hexVBC_step3 h0

/--
[hexVBC_step4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean)
-/
@[path]
private lemma hexVBC_step4_eq
-- given
  (h0 : ℤ) :
-- imply
  halfStep (h0 + 4) = (((-1 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
-- proof
  apply StatMech.Universality.hexVBC_step4 h0

/--
[hexVBC_step5](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean)
-/
@[path]
private lemma hexVBC_step5_eq
-- given
  (h0 : ℤ) :
-- imply
  halfStep (h0 + 5) = (((0 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
-- proof
  apply StatMech.Universality.hexVBC_step5 h0

/--
[hexVBC_halfStep_classify](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean)
-/
@[path]
private lemma hexVBC_halfStep_classify_eq
-- given
  (h0 h : ℤ) :
-- imply
  ∃ α β : ℝ, halfStep h = ((α : ℂ) + (β : ℂ) * hexOmega) * halfStep h0 ∧ ((α, β) = ((1 : ℝ), (0 : ℝ)) ∨ (α, β) = (1, 1) ∨ (α, β) = (0, 1) ∨ (α, β) = (-1, 0) ∨ (α, β) = (-1, -1) ∨ (α, β) = (0, -1)) := by
-- proof
  apply StatMech.Universality.hexVBC_halfStep_classify h0 h

/--
[hexVBC_star_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean)
-/
@[path]
private lemma hexVBC_star_mem_eq
  {m s : ℂ}
  {α β : ℝ}
-- given
  (hin : (α, β) = ((1 : ℝ), (0 : ℝ)) ∨ (α, β) = (1, 1) ∨ (α, β) = (0, 1) ∨ (α, β) = (-1, 0) ∨ (α, β) = (-1, -1) ∨ (α, β) = (0, -1)) :
-- imply
  m + ((α : ℂ) + (β : ℂ) * hexOmega) * s ∈ hexVBC_star m s := by
-- proof
  apply StatMech.Universality.hexVBC_star_mem m s α β hin

/--
[hexVBC_vertexBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean)
-/
@[path]
private lemma hexVBC_vertexBound_eq
  {a : ℂ}
  {W : HexWalk}
-- given
  (h0 : ℤ)
  (hmids : ∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) :
-- imply
  ∀ x ∈ W.vertices, x ∈ hexVBC_adjClosure a h0 := by
-- proof
  apply StatMech.Universality.hexVBC_vertexBound a h0 W hmids

/--
[hexVBC_inRegion_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean)
-/
@[path]
private lemma hexVBC_inRegion_iff_eq
  {a : ℂ}
  {z : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  (hexVBCRegion a h0).inRegion z ↔ (z = a ∨ z = hexConcreteQ a h0 ∨ z = hexConcreteR a h0) := by
-- proof
  apply StatMech.Universality.hexVBC_inRegion_iff a h0 z

/--
[hexVBC_region_stay_short](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean)
-/
@[path]
private lemma hexVBC_region_stay_short_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hturns : ∀ t ∈ ts, t = 1 ∨ t = -1)
  (hstay : ∀ m ∈ (ofTurns a h0 ts).mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) :
-- imply
  ts.length ≤ 1 := by
-- proof
  apply StatMech.Universality.hexVBC_region_stay_short a h0 ts hturns hstay

/--
[hexVBC_support_classify](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean)
-/
@[path]
private lemma hexVBC_support_classify_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hlegal : (ofTurns a h0 ts).IsLegalSAW)
  (hstay : (ofTurns a h0 ts).StaysIn (hexVBCRegion a h0).inRegion) :
-- imply
  ts = [] ∨ ts = [-1] ∨ ts = [1] := by
-- proof
  apply StatMech.Universality.hexVBC_support_classify a h0 ts hlegal hstay

/--
[hexVBC_staysIn_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean)
-/
@[path]
private lemma hexVBC_staysIn_p_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  (ofTurns a h0 []).StaysIn (hexVBCRegion a h0).inRegion := by
-- proof
  apply StatMech.Universality.hexVBC_staysIn_p a h0

/--
[hexVBC_staysIn_q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean)
-/
@[path]
private lemma hexVBC_staysIn_q_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  (ofTurns a h0 [-1]).StaysIn (hexVBCRegion a h0).inRegion := by
-- proof
  apply StatMech.Universality.hexVBC_staysIn_q a h0

/--
[hexVBC_staysIn_r](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean)
-/
@[path]
private lemma hexVBC_staysIn_r_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  (ofTurns a h0 [1]).StaysIn (hexVBCRegion a h0).inRegion := by
-- proof
  apply StatMech.Universality.hexVBC_staysIn_r a h0

/--
[hexVBC_covering_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean)
-/
@[path]
private lemma hexVBC_covering_p_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hsupp : ts ∈ Function.support (combinedSummand (hexVBCRegion a h0).inRegion a h0 (hexConcreteV a h0) (hexConcreteDu a h0)))
  (hp : (ofTurns a h0 ts).EndsAt (hexConcreteV a h0 + hexConcreteDu a h0)) :
-- imply
  ts = [] := by
-- proof
  apply StatMech.Universality.hexVBC_covering_p a h0 ts hsupp hp

/--
[hexVBC_covering_q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean)
-/
@[path]
private lemma hexVBC_covering_q_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hsupp : ts ∈ Function.support (combinedSummand (hexVBCRegion a h0).inRegion a h0 (hexConcreteV a h0) (hexConcreteDu a h0)))
  (hq : (ofTurns a h0 ts).EndsAt (hexConcreteV a h0 + hexOmega * hexConcreteDu a h0)) :
-- imply
  ts = [-1] := by
-- proof
  apply StatMech.Universality.hexVBC_covering_q a h0 ts hsupp hq

/--
[hexVBC_covering_r](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean)
-/
@[path]
private lemma hexVBC_covering_r_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hsupp : ts ∈ Function.support (combinedSummand (hexVBCRegion a h0).inRegion a h0 (hexConcreteV a h0) (hexConcreteDu a h0)))
  (hr : (ofTurns a h0 ts).EndsAt (hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0)) :
-- imply
  ts = [1] := by
-- proof
  apply StatMech.Universality.hexVBC_covering_r a h0 ts hsupp hr

/--
[hexVBC_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean)
-/
@[path]
private lemma hexVBC_summable_eq
  {a : ℂ}
  {z : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  Summable fun ts => parafSummand (hexVBCRegion a h0).inRegion a h0 z (5/8) hexChi ts := by
-- proof
  apply StatMech.Universality.hexVBC_summable a h0 z

/--
[hexVBC_obs_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean)
-/
@[path]
private lemma hexVBC_obs_p_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  parafObservable (hexVBCRegion a h0).inRegion a h0 (hexConcreteV a h0 + hexConcreteDu a h0) (5/8) hexChi = parafSummand (hexVBCRegion a h0).inRegion a h0 (hexConcreteV a h0 + hexConcreteDu a h0) (5/8) hexChi [] := by
-- proof
  apply StatMech.Universality.hexVBC_obs_p a h0

/--
[hexVBC_obs_q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean)
-/
@[path]
private lemma hexVBC_obs_q_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  parafObservable (hexVBCRegion a h0).inRegion a h0 (hexConcreteV a h0 + hexOmega * hexConcreteDu a h0) (5/8) hexChi = parafSummand (hexVBCRegion a h0).inRegion a h0 (hexConcreteV a h0 + hexOmega * hexConcreteDu a h0) (5/8) hexChi [-1] := by
-- proof
  apply StatMech.Universality.hexVBC_obs_q a h0

/--
[hexVBC_obs_r](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean)
-/
@[path]
private lemma hexVBC_obs_r_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  parafObservable (hexVBCRegion a h0).inRegion a h0 (hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0) (5/8) hexChi = parafSummand (hexVBCRegion a h0).inRegion a h0 (hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0) (5/8) hexChi [1] := by
-- proof
  apply StatMech.Universality.hexVBC_obs_r a h0

/--
[hexVBC_vertex_relation_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean)
-/
@[path]
private lemma hexVBC_vertex_relation_unconditional_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  ((hexConcreteV a h0 + hexConcreteDu a h0) - hexConcreteV a h0) * parafObservable (hexVBCRegion a h0).inRegion a h0 (hexConcreteV a h0 + hexConcreteDu a h0) (5/8) hexChi + ((hexConcreteV a h0 + hexOmega * hexConcreteDu a h0) - hexConcreteV a h0) * parafObservable (hexVBCRegion a h0).inRegion a h0 (hexConcreteV a h0 + hexOmega * hexConcreteDu a h0) (5/8) hexChi + ((hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0) - hexConcreteV a h0) * parafObservable (hexVBCRegion a h0).inRegion a h0 (hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0) (5/8) hexChi = 0 := by
-- proof
  apply StatMech.Universality.hexVBC_vertex_relation_unconditional a h0


-- created on 2026-10-23
