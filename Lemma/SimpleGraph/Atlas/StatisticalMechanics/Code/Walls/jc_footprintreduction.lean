import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc_footprintreduction
open SimpleGraph Function Set StatMech StatMech.Walls


/--
[jc_orbit_unchanged_of_not_footprint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_footprintreduction.lean)
-/
@[path]
private lemma jc_orbit_unchanged_of_not_footprint_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {c : Site 2}
  {k : ℕ}
-- given
  (hc : c ∉ jc_orbitFootprint K a) :
-- imply
  (dartNext (K \ {c}))^[k] a.1 = (dartNext K)^[k] a.1 := by
-- proof
  apply StatMech.Walls.jc_orbit_unchanged_of_not_footprint K a c hc k

/--
[jc_cornerBalance_unchanged_of_not_footprint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_footprintreduction.lean)
-/
@[path]
private lemma jc_cornerBalance_unchanged_of_not_footprint_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {c : Site 2}
-- given
  (hc : c ∉ jc_orbitFootprint K a)
  (hbd : IsBoundaryDart (K \ {c}) a.1) :
-- imply
  cornerBalance (K \ {c}) ⟨a.1, hbd⟩ = cornerBalance K a := by
-- proof
  apply StatMech.Walls.jc_cornerBalance_unchanged_of_not_footprint K a c hc hbd

/--
[jc_contraction_of_not_saturating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_footprintreduction.lean)
-/
@[path]
private lemma jc_contraction_of_not_saturating_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {c : Site 2}
-- given
  (hK : K.Finite)
  (hcK : c ∈ K)
  (hc : c ∉ jc_orbitFootprint K a) :
-- imply
  ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty) (a' : {e : Dart // IsBoundaryDart K' e}), K'.ncard < K.ncard ∧ cornerBalance K' a' = cornerBalance K a := by
-- proof
  apply StatMech.Walls.jc_contraction_of_not_saturating K hK a c hcK hc

/--
[jc_footprintReduction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_footprintreduction.lean)
-/
@[path]
private lemma jc_footprintReduction_eq
-- given
  (h : jc_BalanceSaturatingContraction) :
-- imply
  BalancePreservingContraction := by
-- proof
  apply StatMech.Walls.jc_footprintReduction h

/--
[jc_footprintReduction_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_footprintreduction.lean)
-/
@[path]
private lemma jc_footprintReduction_iff_eq :
-- imply
  BalancePreservingContraction ↔ jc_BalanceSaturatingContraction := by
-- proof
  apply StatMech.Walls.jc_footprintReduction_iff

/--
[jc_totalTurn_eq_four_of_saturating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_footprintreduction.lean)
-/
@[path]
private lemma jc_totalTurn_eq_four_of_saturating_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hSK : (ndt_StarHull K).Finite)
  (hne : (ndt_StarHull K).Nonempty)
  (hsat : jc_BalanceSaturatingContraction) :
-- imply
  TurningIsFullRevolution (ndt_StarHull K) a := by
-- proof
  apply StatMech.Walls.jc_totalTurn_eq_four_of_saturating K hSK hne a hsat

/--
[jc_totalTurn_eq_four_value_of_saturating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_footprintreduction.lean)
-/
@[path]
private lemma jc_totalTurn_eq_four_value_of_saturating_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hSK : (ndt_StarHull K).Finite)
  (hne : (ndt_StarHull K).Nonempty)
  (hsat : jc_BalanceSaturatingContraction) :
-- imply
  totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨ totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 := by
-- proof
  apply StatMech.Walls.jc_totalTurn_eq_four_value_of_saturating K hSK hne a hsat

/--
[jc_domino_saturating_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_footprintreduction.lean)
-/
@[path]
private lemma jc_domino_saturating_witness_eq :
-- imply
  ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty) (a' : {e : Dart // IsBoundaryDart K' e}), K'.ncard < domino.ncard ∧ cornerBalance K' a' = cornerBalance domino dmBase := by
-- proof
  apply StatMech.Walls.jc_domino_saturating_witness


-- created on 2026-10-23
