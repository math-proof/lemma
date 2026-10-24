import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.jc4_iteratecoincide
open SimpleGraph Function Set StatMech StatMech.Walls


/--
[jc4_iterate_coincide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_iteratecoincide.lean)
-/
@[path]
private lemma jc4_iterate_coincide_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {k : ℕ}
-- given
  (hnp : ∀ i, bpc_NotProbed r ((dartNext K)^[i] a.1)) :
-- imply
  (dartNext (K \ {r}))^[k] a.1 = (dartNext K)^[k] a.1 := by
-- proof
  apply StatMech.Walls.jc4_iterate_coincide K a r hnp k

/--
[jc4_basepoint_survives](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_iteratecoincide.lean)
-/
@[path]
private lemma jc4_basepoint_survives_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hne : r ≠ a.1.tail) :
-- imply
  IsBoundaryDart (K \ {r}) a.1 := by
-- proof
  apply StatMech.Walls.jc4_basepoint_survives K a r hne

/--
[jc4_period_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_iteratecoincide.lean)
-/
@[path]
private lemma jc4_period_eq_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hnp : ∀ i, bpc_NotProbed r ((dartNext K)^[i] a.1))
  (hne : r ≠ a.1.tail) :
-- imply
  dartOrbitPeriod (K \ {r}) ⟨a.1, jc4_basepoint_survives K a r hne⟩ = dartOrbitPeriod K a := by
-- proof
  apply StatMech.Walls.jc4_period_eq K a r hnp hne

/--
[jc4_iterate_coincide_and_period_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_iteratecoincide.lean)
-/
@[path]
private lemma jc4_iterate_coincide_and_period_eq_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hnp : ∀ i, bpc_NotProbed r ((dartNext K)^[i] a.1))
  (hne : r ≠ a.1.tail) :
-- imply
  ∃ a' : {e : Dart // IsBoundaryDart (K \ {r}) e}, a'.1 = a.1 ∧ (∀ k, (dartNext (K \ {r}))^[k] a'.1 = (dartNext K)^[k] a.1) ∧ dartOrbitPeriod (K \ {r}) a' = dartOrbitPeriod K a := by
-- proof
  apply StatMech.Walls.jc4_iterate_coincide_and_period_eq K a r hnp hne

/--
[jc4_turn_coincide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_iteratecoincide.lean)
-/
@[path]
private lemma jc4_turn_coincide_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {i : ℕ}
-- given
  (hnp : ∀ i, bpc_NotProbed r ((dartNext K)^[i] a.1)) :
-- imply
  turnZ (K \ {r}) ((dartNext (K \ {r}))^[i] a.1) = turnZ K ((dartNext K)^[i] a.1) := by
-- proof
  apply StatMech.Walls.jc4_turn_coincide K a r hnp i

/--
[jc4_degenerate_orbitSplice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_iteratecoincide.lean)
-/
@[path]
private lemma jc4_degenerate_orbitSplice_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hnp : ∀ i, bpc_NotProbed r ((dartNext K)^[i] a.1))
  (hne : r ≠ a.1.tail)
  (hne' : (K \ {r}).Nonempty) :
-- imply
  jc3_OrbitSpliceDatum K a r := by
-- proof
  apply StatMech.Walls.jc4_degenerate_orbitSplice K a r hnp hne hne'

/--
[jc4_footprintDisjoint_of_not_footprint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_iteratecoincide.lean)
-/
@[path]
private lemma jc4_footprintDisjoint_of_not_footprint_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hr : r ∉ bpc_orbitFootprint K a) :
-- imply
  (∀ i, bpc_NotProbed r ((dartNext K)^[i] a.1)) ∧ r ≠ a.1.tail := by
-- proof
  apply StatMech.Walls.jc4_footprintDisjoint_of_not_footprint K a r hr

/--
[jc4_not_saturating_of_footprintDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_iteratecoincide.lean)
-/
@[path]
private lemma jc4_not_saturating_of_footprintDisjoint_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hsat : ¬ K ⊆ bpc_orbitFootprint K a) :
-- imply
  ∃ r, r ∈ K ∧ (∀ i, bpc_NotProbed r ((dartNext K)^[i] a.1)) ∧ r ≠ a.1.tail := by
-- proof
  apply StatMech.Walls.jc4_not_saturating_of_footprintDisjoint K a hsat

/--
[jc4_footprintDisjoint_iff_not_footprint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_iteratecoincide.lean)
-/
@[path]
private lemma jc4_footprintDisjoint_iff_not_footprint_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2} :
-- imply
  r ∉ bpc_orbitFootprint K a ↔ (∀ i, bpc_NotProbed r ((dartNext K)^[i] a.1)) ∧ (∀ i, r ≠ ((dartNext K)^[i] a.1).tail) := by
-- proof
  apply StatMech.Walls.jc4_footprintDisjoint_iff_not_footprint K a r

/--
[jc4_cornerBalance_coincide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_iteratecoincide.lean)
-/
@[path]
private lemma jc4_cornerBalance_coincide_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hnp : ∀ i, bpc_NotProbed r ((dartNext K)^[i] a.1))
  (hne : r ≠ a.1.tail) :
-- imply
  cornerBalance (K \ {r}) ⟨a.1, jc4_basepoint_survives K a r hne⟩ = cornerBalance K a := by
-- proof
  apply StatMech.Walls.jc4_cornerBalance_coincide K a r hnp hne

/--
[jc4_farCell_coincide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_iteratecoincide.lean)
-/
@[path]
private lemma jc4_farCell_coincide_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {k : ℕ}
-- given
  (hr : r ∉ bpc_orbitFootprint K a) :
-- imply
  (dartNext (K \ {r}))^[k] a.1 = (dartNext K)^[k] a.1 := by
-- proof
  apply StatMech.Walls.jc4_farCell_coincide K a r hr k

/--
[jc4_farCell_degenerate_orbitSplice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_iteratecoincide.lean)
-/
@[path]
private lemma jc4_farCell_degenerate_orbitSplice_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hr : r ∉ bpc_orbitFootprint K a)
  (hne' : (K \ {r}).Nonempty) :
-- imply
  jc3_OrbitSpliceDatum K a r := by
-- proof
  apply StatMech.Walls.jc4_farCell_degenerate_orbitSplice K a r hr hne'


-- created on 2026-10-23
