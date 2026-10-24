import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.jc5_core
open SimpleGraph Function Set StatMech StatMech.Walls


/--
[jc5_tailFootprintFree_of_noReentry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_core.lean)
-/
@[path]
private lemma jc5_tailFootprintFree_of_noReentry_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
  (hnore : jc5_NoReentry K a r) :
-- imply
  jc4_TailFootprintFree K a r (jc4_firstReturnK K a r hex) (dartOrbitPeriod K a - jc4_firstReturnK K a r hex) := by
-- proof
  apply StatMech.Walls.jc5_tailFootprintFree_of_noReentry K a r hex hnore

/--
[jc5_noReentry_of_convex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_core.lean)
-/
@[path]
private lemma jc5_noReentry_of_convex_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (ha0 : ¬ jc4_FootprintFree K a r 0)
  (hconv : jc5_TouchingConvex K a r) :
-- imply
  jc5_NoReentry K a r := by
-- proof
  apply StatMech.Walls.jc5_noReentry_of_convex K a r ha0 hconv

/--
[jc5_tailFootprintFree_of_convex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_core.lean)
-/
@[path]
private lemma jc5_tailFootprintFree_of_convex_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
  (ha0 : ¬ jc4_FootprintFree K a r 0)
  (hconv : jc5_TouchingConvex K a r) :
-- imply
  jc4_TailFootprintFree K a r (jc4_firstReturnK K a r hex) (dartOrbitPeriod K a - jc4_firstReturnK K a r hex) := by
-- proof
  apply StatMech.Walls.jc5_tailFootprintFree_of_convex K a r hex ha0 hconv

/--
[jc5_period_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_core.lean)
-/
@[path]
private lemma jc5_period_decomp_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
  (hle : jc4_firstReturnK K a r hex ≤ dartOrbitPeriod K a) :
-- imply
  dartOrbitPeriod K a = jc4_firstReturnK K a r hex + (dartOrbitPeriod K a - jc4_firstReturnK K a r hex) := by
-- proof
  apply StatMech.Walls.jc5_period_decomp K a r hex hle

/--
[jc5_orbitSpliceDatum_of_noReentry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_core.lean)
-/
@[path]
private lemma jc5_orbitSpliceDatum_of_noReentry_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {a' : {e : Dart // IsBoundaryDart (K \ {r}) e}}
  {m' : ℕ}
-- given
  (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
  (hnore : jc5_NoReentry K a r)
  (hne' : (K \ {r}).Nonempty)
  (hp : dartOrbitPeriod K a = jc4_firstReturnK K a r hex + (dartOrbitPeriod K a - jc4_firstReturnK K a r hex))
  (hp' : dartOrbitPeriod (K \ {r}) a' = m' + (dartOrbitPeriod K a - jc4_firstReturnK K a r hex))
  (heq : ∀ i, i < dartOrbitPeriod K a - jc4_firstReturnK K a r hex → (dartNext (K \ {r}))^[m' + i] a'.1 = (dartNext K)^[jc4_firstReturnK K a r hex + i] a.1)
  (hbal : jc_windowTurn (K \ {r}) a'.1 0 m' = jc_windowTurn K a.1 0 (jc4_firstReturnK K a r hex)) :
-- imply
  jc3_OrbitSpliceDatum K a r := by
-- proof
  apply StatMech.Walls.jc5_orbitSpliceDatum_of_noReentry K a r hex hnore hne' a' m' hp hp' heq hbal

/--
[jc5_noReentry_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_core.lean)
-/
@[path]
private lemma jc5_noReentry_of_disjoint_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hfoot : ∀ i, jc4_FootprintFree K a r i) :
-- imply
  jc5_NoReentry K a r := by
-- proof
  apply StatMech.Walls.jc5_noReentry_of_disjoint K a r hfoot

/--
[jc5_touchingConvex_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_core.lean)
-/
@[path]
private lemma jc5_touchingConvex_of_disjoint_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hfoot : ∀ i, jc4_FootprintFree K a r i) :
-- imply
  jc5_TouchingConvex K a r := by
-- proof
  apply StatMech.Walls.jc5_touchingConvex_of_disjoint K a r hfoot

/--
[jc5_noReentry_of_avoids](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_core.lean)
-/
@[path]
private lemma jc5_noReentry_of_avoids_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hfoot : ∀ i, jc3_AvoidsEarFootprint r ((dartNext K)^[i] a.1)) :
-- imply
  jc5_NoReentry K a r := by
-- proof
  apply StatMech.Walls.jc5_noReentry_of_avoids K a r hfoot

/--
[jc5_orbit_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_core.lean)
-/
@[path]
private lemma jc5_orbit_isCycle_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite) :
-- imply
  (dartOrbitWalk K a).IsCycle := by
-- proof
  apply StatMech.Walls.jc5_orbit_isCycle K hK a

/--
[jc5_touchingDarts_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_core.lean)
-/
@[path]
private lemma jc5_touchingDarts_finite_eq
  {r : Site 2} :
-- imply
  {e : Dart | jc5_ProbesEarFootprint r e}.Finite := by
-- proof
  apply StatMech.Walls.jc5_touchingDarts_finite r

/--
[jc5_firstReturn_landmark](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_core.lean)
-/
@[path]
private lemma jc5_firstReturn_landmark_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
  (ha0 : ¬ jc4_FootprintFree K a r 0) :
-- imply
  (1 ≤ jc4_firstReturnK K a r hex ∧ jc4_FootprintFree K a r (jc4_firstReturnK K a r hex) ∧ (∀ k, 1 ≤ k → jc4_FootprintFree K a r k → jc4_firstReturnK K a r hex ≤ k)) ∧ (∀ k, k < jc4_firstReturnK K a r hex → ¬ jc4_FootprintFree K a r k) := by
-- proof
  apply StatMech.Walls.jc5_firstReturn_landmark K a r hex ha0

/--
[jc5_excursionConfined_of_noReentry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_core.lean)
-/
@[path]
private lemma jc5_excursionConfined_of_noReentry_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
  (hnore : jc5_NoReentry K a r) :
-- imply
  jc5_ExcursionConfined K a r hex := by
-- proof
  apply StatMech.Walls.jc5_excursionConfined_of_noReentry K a r hex hnore

/--
[jc5_excursionConfined_of_convex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_core.lean)
-/
@[path]
private lemma jc5_excursionConfined_of_convex_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
  (ha0 : ¬ jc4_FootprintFree K a r 0)
  (hconv : jc5_TouchingConvex K a r) :
-- imply
  jc5_ExcursionConfined K a r hex := by
-- proof
  apply StatMech.Walls.jc5_excursionConfined_of_convex K a r hex ha0 hconv


-- created on 2026-10-23
