import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.BalanceContraction.Part2
open SimpleGraph Function StatMech StatMech.Lattice


/--
[sum_range_cyclic_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalanceContraction.lean)
-/
@[path]
private lemma sum_range_cyclic_shift_eq
  {g : ℕ → ℤ}
  {p : ℕ}
-- given
  (hcyc : g p = g 0) :
-- imply
  ∑ i ∈ Finset.range p, g (i + 1) = ∑ i ∈ Finset.range p, g i := by
-- proof
  apply StatMech.Lattice.sum_range_cyclic_shift g p hcyc

/--
[dartOrbitPeriod_dartNextSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalanceContraction.lean)
-/
@[path]
private lemma dartOrbitPeriod_dartNextSub_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite) :
-- imply
  dartOrbitPeriod K (dartNextSub K a) = dartOrbitPeriod K a := by
-- proof
  apply StatMech.Lattice.dartOrbitPeriod_dartNextSub K hK a

/--
[dartOrbitPeriod_iterate_dartNextSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalanceContraction.lean)
-/
@[path]
private lemma dartOrbitPeriod_iterate_dartNextSub_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {n : ℕ}
-- given
  (hK : K.Finite) :
-- imply
  dartOrbitPeriod K ((dartNextSub K)^[n] a) = dartOrbitPeriod K a := by
-- proof
  apply StatMech.Lattice.dartOrbitPeriod_iterate_dartNextSub K hK a n

/--
[totalTurnZ_period_dartNextSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalanceContraction.lean)
-/
@[path]
private lemma totalTurnZ_period_dartNextSub_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite) :
-- imply
  totalTurnZ K (dartNextSub K a).1 (dartOrbitPeriod K (dartNextSub K a)) = totalTurnZ K a.1 (dartOrbitPeriod K a) := by
-- proof
  apply StatMech.Lattice.totalTurnZ_period_dartNextSub K hK a

/--
[totalTurnZ_period_iterate_dartNextSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalanceContraction.lean)
-/
@[path]
private lemma totalTurnZ_period_iterate_dartNextSub_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {n : ℕ}
-- given
  (hK : K.Finite) :
-- imply
  totalTurnZ K ((dartNextSub K)^[n] a).1 (dartOrbitPeriod K ((dartNextSub K)^[n] a)) = totalTurnZ K a.1 (dartOrbitPeriod K a) := by
-- proof
  apply StatMech.Lattice.totalTurnZ_period_iterate_dartNextSub K hK a n

/--
[cornerBalance_dartNextSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalanceContraction.lean)
-/
@[path]
private lemma cornerBalance_dartNextSub_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite) :
-- imply
  cornerBalance K (dartNextSub K a) = cornerBalance K a := by
-- proof
  apply StatMech.Lattice.cornerBalance_dartNextSub K hK a

/--
[cornerBalance_iterate_dartNextSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalanceContraction.lean)
-/
@[path]
private lemma cornerBalance_iterate_dartNextSub_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {n : ℕ}
-- given
  (hK : K.Finite) :
-- imply
  cornerBalance K ((dartNextSub K)^[n] a) = cornerBalance K a := by
-- proof
  apply StatMech.Lattice.cornerBalance_iterate_dartNextSub K hK a n

/--
[cornerBalance_constant_on_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalanceContraction.lean)
-/
@[path]
private lemma cornerBalance_constant_on_orbit_eq
  {K : Set (Site 2)}
  {a b : {e : Dart // IsBoundaryDart K e}}
  {n : ℕ}
-- given
  (hK : K.Finite)
  (hb : b = (dartNextSub K)^[n] a) :
-- imply
  cornerBalance K b = cornerBalance K a := by
-- proof
  apply StatMech.Lattice.cornerBalance_constant_on_orbit K hK a b n hb

/--
[revCount_dartNextSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalanceContraction.lean)
-/
@[path]
private lemma revCount_dartNextSub_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite) :
-- imply
  revCount K (dartNextSub K a) = revCount K a := by
-- proof
  apply StatMech.Lattice.revCount_dartNextSub K hK a

/--
[revCount_iterate_dartNextSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalanceContraction.lean)
-/
@[path]
private lemma revCount_iterate_dartNextSub_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {n : ℕ}
-- given
  (hK : K.Finite) :
-- imply
  revCount K ((dartNextSub K)^[n] a) = revCount K a := by
-- proof
  apply StatMech.Lattice.revCount_iterate_dartNextSub K hK a n

/--
[eulerCharOne_dartNextSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalanceContraction.lean)
-/
@[path]
private lemma eulerCharOne_dartNextSub_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite) :
-- imply
  EulerCharOne K (dartNextSub K a) ↔ EulerCharOne K a := by
-- proof
  apply StatMech.Lattice.eulerCharOne_dartNextSub K hK a

/--
[eulerCharOne_iterate_dartNextSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalanceContraction.lean)
-/
@[path]
private lemma eulerCharOne_iterate_dartNextSub_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {n : ℕ}
-- given
  (hK : K.Finite) :
-- imply
  EulerCharOne K ((dartNextSub K)^[n] a) ↔ EulerCharOne K a := by
-- proof
  apply StatMech.Lattice.eulerCharOne_iterate_dartNextSub K hK a n

/--
[cornerBalance_eq_four_revCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalanceContraction.lean)
-/
@[path]
private lemma cornerBalance_eq_four_revCount_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  cornerBalance K a = 4 * revCount K a := by
-- proof
  apply StatMech.Lattice.cornerBalance_eq_four_revCount K a

/--
[balanceIsFour_iff_revCount_pm_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalanceContraction.lean)
-/
@[path]
private lemma balanceIsFour_iff_revCount_pm_one_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  BalanceIsFour K a ↔ (revCount K a = 1 ∨ revCount K a = -1) := by
-- proof
  apply StatMech.Lattice.balanceIsFour_iff_revCount_pm_one K a

/--
[eulerCharOne_iff_balanceIsFour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalanceContraction.lean)
-/
@[path]
private lemma eulerCharOne_iff_balanceIsFour_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a) :
-- imply
  EulerCharOne K a ↔ BalanceIsFour K a := by
-- proof
  apply StatMech.Lattice.eulerCharOne_iff_balanceIsFour K a hp

/--
[balancePreservingContraction_of_rep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalanceContraction.lean)
-/
@[path]
private lemma balancePreservingContraction_of_rep_eq
-- given
  (h : BalancePreservingContractionRep) :
-- imply
  BalancePreservingContraction := by
-- proof
  apply StatMech.Lattice.balancePreservingContraction_of_rep h

/--
[balancePreservingContractionRep_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalanceContraction.lean)
-/
@[path]
private lemma balancePreservingContractionRep_iff_eq :
-- imply
  BalancePreservingContractionRep ↔ BalancePreservingContraction := by
-- proof
  apply StatMech.Lattice.balancePreservingContractionRep_iff

/--
[unitCell_cornerBalance_dartNextSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalanceContraction.lean)
-/
@[path]
private lemma unitCell_cornerBalance_dartNextSub_eq :
-- imply
  cornerBalance unitCell (dartNextSub unitCell ucBase) = cornerBalance unitCell ucBase := by
-- proof
  apply StatMech.Lattice.unitCell_cornerBalance_dartNextSub

/--
[domino_cornerBalance_dartNextSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalanceContraction.lean)
-/
@[path]
private lemma domino_cornerBalance_dartNextSub_eq :
-- imply
  cornerBalance domino (dartNextSub domino dmBase) = cornerBalance domino dmBase := by
-- proof
  apply StatMech.Lattice.domino_cornerBalance_dartNextSub


-- created on 2026-10-23
