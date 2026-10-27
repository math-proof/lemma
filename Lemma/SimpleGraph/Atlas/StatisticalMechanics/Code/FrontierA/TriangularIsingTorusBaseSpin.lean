import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusBaseSpin
open StatMech StatMech.FrontierA


/--
[triangularTorusSurfaceSpin_zero_zero_quadratic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusBaseSpin.lean)
-/
@[path]
private lemma triangularTorusSurfaceSpin_zero_zero_quadratic_eq
  {x y : Fin 2} :
-- imply
  surfaceQuadraticParity (triangularTorusSurfaceSpin 0 0) (fun _ : Fin 1 => x, fun _ : Fin 1 => y) = if x = 0 ∧ y = 0 then 0 else 1 := by
-- proof
  apply StatMech.FrontierA.triangularTorusSurfaceSpin_zero_zero_quadratic x y

/--
[triangularTorusSurfaceSpin_zero_zero_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusBaseSpin.lean)
-/
@[path]
private lemma triangularTorusSurfaceSpin_zero_zero_sign_eq
  {x y : Fin 2} :
-- imply
  (surfaceParitySign (surfaceQuadraticParity (triangularTorusSurfaceSpin 0 0) (fun _ : Fin 1 => x, fun _ : Fin 1 => y)) : Complex) = if x = 0 ∧ y = 0 then 1 else -1 := by
-- proof
  apply StatMech.FrontierA.triangularTorusSurfaceSpin_zero_zero_sign x y

/--
[triangularTorusCycle_baseSpinSign_eq_windingParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusBaseSpin.lean)
-/
@[path]
private lemma triangularTorusCycle_baseSpinSign_eq_windingParity_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
  {mx my : Int}
-- given
  (hp : p.IsCycle)
  (hdisplacement : ∑ k, triangularIntStep (triangularTorusCycleNativeDart L p k).2 = ((L : Int) * mx, (L : Int) * my)) :
-- imply
  (surfaceParitySign (surfaceQuadraticParity (triangularTorusSurfaceSpin 0 0) (surfaceSubgraphHomology (triangularTorusSurfaceEdgeClass L) p.edges.toFinset)) : Complex) = if StatMech.Onsager.ons_intParity mx = 0 ∧ StatMech.Onsager.ons_intParity my = 0 then 1 else -1 := by
-- proof
  apply StatMech.FrontierA.triangularTorusCycle_baseSpinSign_eq_windingParity L p hp mx my hdisplacement

/--
[triangularTorusCycle_surfaceHomology_eq_zero_iff_windingParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusBaseSpin.lean)
-/
@[path]
private lemma triangularTorusCycle_surfaceHomology_eq_zero_iff_windingParity_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
  {mx my : Int}
-- given
  (hp : p.IsCycle)
  (hdisplacement : ∑ k, triangularIntStep (triangularTorusCycleNativeDart L p k).2 = ((L : Int) * mx, (L : Int) * my)) :
-- imply
  surfaceSubgraphHomology (triangularTorusSurfaceEdgeClass L) p.edges.toFinset = 0 ↔ StatMech.Onsager.ons_intParity mx = 0 ∧ StatMech.Onsager.ons_intParity my = 0 := by
-- proof
  apply StatMech.FrontierA.triangularTorusCycle_surfaceHomology_eq_zero_iff_windingParity L p hp mx my hdisplacement

/--
[exists_triangularTorusCycle_nonzeroHomology_periodicLift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusBaseSpin.lean)
-/
@[path]
private lemma exists_triangularTorusCycle_nonzeroHomology_periodicLift_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
-- given
  (hp : p.IsCycle)
  (hhom : surfaceSubgraphHomology (triangularTorusSurfaceEdgeClass L) p.edges.toFinset ≠ 0) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ exists mx my : Int, (∑ k, triangularIntStep (triangularTorusCycleNativeDart L p k).2) = ((L : Int) * mx, (L : Int) * my) ∧ (mx ≠ 0 ∨ my ≠ 0) ∧ Function.Injective (triangularIntPeriodicPos (fun k => (triangularTorusCycleNativeDart L p k).2)) := by
-- proof
  apply StatMech.FrontierA.exists_triangularTorusCycle_nonzeroHomology_periodicLift L p hp hhom


-- created on 2026-10-23
