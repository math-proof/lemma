import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc_orbitinvariant.Part3
open SimpleGraph Function StatMech StatMech.Walls


/--
[jc_sum_range_cyclic_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_orbitinvariant.lean)
-/
@[path]
private lemma jc_sum_range_cyclic_shift_eq
  {g : ℕ → ℤ}
  {p : ℕ}
-- given
  (hcyc : g p = g 0) :
-- imply
  ∑ i ∈ Finset.range p, g (i + 1) = ∑ i ∈ Finset.range p, g i := by
-- proof
  apply StatMech.Walls.jc_sum_range_cyclic_shift g p hcyc

/--
[jc_dartOrbitPeriod_dartNextSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_orbitinvariant.lean)
-/
@[path]
private lemma jc_dartOrbitPeriod_dartNextSub_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite) :
-- imply
  dartOrbitPeriod K (dartNextSub K a) = dartOrbitPeriod K a := by
-- proof
  apply StatMech.Walls.jc_dartOrbitPeriod_dartNextSub K hK a

/--
[jc_dartOrbitPeriod_iterate_dartNextSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_orbitinvariant.lean)
-/
@[path]
private lemma jc_dartOrbitPeriod_iterate_dartNextSub_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {n : ℕ}
-- given
  (hK : K.Finite) :
-- imply
  dartOrbitPeriod K ((dartNextSub K)^[n] a) = dartOrbitPeriod K a := by
-- proof
  apply StatMech.Walls.jc_dartOrbitPeriod_iterate_dartNextSub K hK a n

/--
[jc_totalTurnZ_period_dartNextSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_orbitinvariant.lean)
-/
@[path]
private lemma jc_totalTurnZ_period_dartNextSub_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite) :
-- imply
  totalTurnZ K (dartNextSub K a).1 (dartOrbitPeriod K (dartNextSub K a)) = totalTurnZ K a.1 (dartOrbitPeriod K a) := by
-- proof
  apply StatMech.Walls.jc_totalTurnZ_period_dartNextSub K hK a

/--
[jc_totalTurnZ_period_iterate_dartNextSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_orbitinvariant.lean)
-/
@[path]
private lemma jc_totalTurnZ_period_iterate_dartNextSub_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {n : ℕ}
-- given
  (hK : K.Finite) :
-- imply
  totalTurnZ K ((dartNextSub K)^[n] a).1 (dartOrbitPeriod K ((dartNextSub K)^[n] a)) = totalTurnZ K a.1 (dartOrbitPeriod K a) := by
-- proof
  apply StatMech.Walls.jc_totalTurnZ_period_iterate_dartNextSub K hK a n

/--
[jc_cornerBalance_dartNextSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_orbitinvariant.lean)
-/
@[path]
private lemma jc_cornerBalance_dartNextSub_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite) :
-- imply
  cornerBalance K (dartNextSub K a) = cornerBalance K a := by
-- proof
  apply StatMech.Walls.jc_cornerBalance_dartNextSub K hK a

/--
[jc_cornerBalance_iterate_dartNextSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_orbitinvariant.lean)
-/
@[path]
private lemma jc_cornerBalance_iterate_dartNextSub_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {n : ℕ}
-- given
  (hK : K.Finite) :
-- imply
  cornerBalance K ((dartNextSub K)^[n] a) = cornerBalance K a := by
-- proof
  apply StatMech.Walls.jc_cornerBalance_iterate_dartNextSub K hK a n

/--
[jc_cornerBalance_constant_on_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_orbitinvariant.lean)
-/
@[path]
private lemma jc_cornerBalance_constant_on_orbit_eq
  {K : Set (Site 2)}
  {a b : {e : Dart // IsBoundaryDart K e}}
  {n : ℕ}
-- given
  (hK : K.Finite)
  (hb : b = (dartNextSub K)^[n] a) :
-- imply
  cornerBalance K b = cornerBalance K a := by
-- proof
  apply StatMech.Walls.jc_cornerBalance_constant_on_orbit K hK a b n hb

/--
[jc_balancePreservingContraction_of_rep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_orbitinvariant.lean)
-/
@[path]
private lemma jc_balancePreservingContraction_of_rep_eq
-- given
  (h : jc_BalancePreservingContractionRep) :
-- imply
  BalancePreservingContraction := by
-- proof
  apply StatMech.Walls.jc_balancePreservingContraction_of_rep h

/--
[jc_balancePreservingContractionRep_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_orbitinvariant.lean)
-/
@[path]
private lemma jc_balancePreservingContractionRep_iff_eq :
-- imply
  jc_BalancePreservingContractionRep ↔ BalancePreservingContraction := by
-- proof
  apply StatMech.Walls.jc_balancePreservingContractionRep_iff

/--
[jc_balancePreservingContractionExtreme_of_rep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_orbitinvariant.lean)
-/
@[path]
private lemma jc_balancePreservingContractionExtreme_of_rep_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (h : jc_BalancePreservingContractionExtreme)
  (hK : K.Finite)
  (hge : 2 ≤ K.ncard)
  (hc : IsExtremeCell K c) :
-- imply
  ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty) (a' : {e : Dart // IsBoundaryDart K' e}), K'.ncard < K.ncard ∧ cornerBalance K' a' = cornerBalance K (extremeBase K c hc) := by
-- proof
  apply StatMech.Walls.jc_balancePreservingContractionExtreme_of_rep h K hK hge c hc

/--
[jc_balancePreservingContraction_at_orbit_of_extreme](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_orbitinvariant.lean)
-/
@[path]
private lemma jc_balancePreservingContraction_at_orbit_of_extreme_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {a : {e : Dart // IsBoundaryDart K e}}
  {n : ℕ}
-- given
  (h : jc_BalancePreservingContractionExtreme)
  (hK : K.Finite)
  (hge : 2 ≤ K.ncard)
  (hc : IsExtremeCell K c)
  (ha : a = (dartNextSub K)^[n] (extremeBase K c hc)) :
-- imply
  ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty) (a' : {e : Dart // IsBoundaryDart K' e}), K'.ncard < K.ncard ∧ cornerBalance K' a' = cornerBalance K a := by
-- proof
  apply StatMech.Walls.jc_balancePreservingContraction_at_orbit_of_extreme h K hK hge c hc a n ha

/--
[jc_unitCell_cornerBalance_dartNextSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_orbitinvariant.lean)
-/
@[path]
private lemma jc_unitCell_cornerBalance_dartNextSub_eq :
-- imply
  cornerBalance unitCell (dartNextSub unitCell ucBase) = cornerBalance unitCell ucBase := by
-- proof
  apply StatMech.Walls.jc_unitCell_cornerBalance_dartNextSub

/--
[jc_domino_cornerBalance_dartNextSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_orbitinvariant.lean)
-/
@[path]
private lemma jc_domino_cornerBalance_dartNextSub_eq :
-- imply
  cornerBalance domino (dartNextSub domino dmBase) = cornerBalance domino dmBase := by
-- proof
  apply StatMech.Walls.jc_domino_cornerBalance_dartNextSub


-- created on 2026-10-23
