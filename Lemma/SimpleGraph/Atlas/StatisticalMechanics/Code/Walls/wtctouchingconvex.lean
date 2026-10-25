import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.wtctouchingconvex.Part3
open SimpleGraph Function Set StatMech StatMech.Walls


/--
[wtc_touching_iff_probes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wtctouchingconvex.lean)
-/
@[path]
private lemma wtc_touching_iff_probes_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {i : ℕ} :
-- imply
  ¬ jc4_FootprintFree K a r i ↔ jc5_ProbesEarFootprint r ((dartNext K)^[i] a.1) := by
-- proof
  apply StatMech.Walls.wtc_touching_iff_probes K a r i

/--
[wtc_free_iff_avoids](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wtctouchingconvex.lean)
-/
@[path]
private lemma wtc_free_iff_avoids_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {i : ℕ} :
-- imply
  jc4_FootprintFree K a r i ↔ jc3_AvoidsEarFootprint r ((dartNext K)^[i] a.1) := by
-- proof
  apply StatMech.Walls.wtc_free_iff_avoids K a r i

/--
[wtc_touchingSteps_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wtctouchingconvex.lean)
-/
@[path]
private lemma wtc_touchingSteps_injOn_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2} :
-- imply
  Set.InjOn (fun i => (dartNext K)^[i] a.1) (wtc_touchingSteps K a r) := by
-- proof
  apply StatMech.Walls.wtc_touchingSteps_injOn K a r

/--
[wtc_touchingSteps_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wtctouchingconvex.lean)
-/
@[path]
private lemma wtc_touchingSteps_finite_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2} :
-- imply
  (wtc_touchingSteps K a r).Finite := by
-- proof
  apply StatMech.Walls.wtc_touchingSteps_finite K a r

/--
[wtc_touchingConvex_windowed_of_dartsConvex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wtctouchingconvex.lean)
-/
@[path]
private lemma wtc_touchingConvex_windowed_of_dartsConvex_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hconv : wtc_TouchingDartsConvex K a r) :
-- imply
  ∀ i j k, i < j → j < k → k < dartOrbitPeriod K a → ¬ jc4_FootprintFree K a r i → ¬ jc4_FootprintFree K a r k → ¬ jc4_FootprintFree K a r j := by
-- proof
  apply StatMech.Walls.wtc_touchingConvex_windowed_of_dartsConvex K a r hconv

/--
[wtc_touchingDartsConvex_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wtctouchingconvex.lean)
-/
@[path]
private lemma wtc_touchingDartsConvex_of_disjoint_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hfoot : ∀ i, ¬ jc5_ProbesEarFootprint r ((dartNext K)^[i] a.1)) :
-- imply
  wtc_TouchingDartsConvex K a r := by
-- proof
  apply StatMech.Walls.wtc_touchingDartsConvex_of_disjoint K a r hfoot

/--
[wtc_touchingConvex_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wtctouchingconvex.lean)
-/
@[path]
private lemma wtc_touchingConvex_of_disjoint_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hfoot : ∀ i, jc4_FootprintFree K a r i) :
-- imply
  jc5_TouchingConvex K a r := by
-- proof
  apply StatMech.Walls.wtc_touchingConvex_of_disjoint K a r hfoot


-- created on 2026-10-23
