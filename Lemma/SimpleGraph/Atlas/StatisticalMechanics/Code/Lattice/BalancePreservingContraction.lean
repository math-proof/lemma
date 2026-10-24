import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.BalancePreservingContraction
open SimpleGraph Function Set StatMech StatMech.Lattice


/--
[bpc_dartNext_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalancePreservingContraction.lean)
-/
@[path]
private lemma bpc_dartNext_agree_eq
  {K K' : Set (Site 2)}
  {e : Dart}
-- given
  (h0 : (e.head + (-rot90Fun e.dir) ∈ K') ↔ (e.head + (-rot90Fun e.dir) ∈ K))
  (h1 : (e.tail + (-rot90Fun e.dir) ∈ K') ↔ (e.tail + (-rot90Fun e.dir) ∈ K)) :
-- imply
  dartNext K' e = dartNext K e := by
-- proof
  apply StatMech.Lattice.bpc_dartNext_agree K K' e h0 h1

/--
[bpc_turnZ_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalancePreservingContraction.lean)
-/
@[path]
private lemma bpc_turnZ_agree_eq
  {K K' : Set (Site 2)}
  {e : Dart}
-- given
  (h0 : (e.head + (-rot90Fun e.dir) ∈ K') ↔ (e.head + (-rot90Fun e.dir) ∈ K))
  (h1 : (e.tail + (-rot90Fun e.dir) ∈ K') ↔ (e.tail + (-rot90Fun e.dir) ∈ K)) :
-- imply
  turnZ K' e = turnZ K e := by
-- proof
  apply StatMech.Lattice.bpc_turnZ_agree K K' e h0 h1

/--
[bpc_dartNext_diff_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalancePreservingContraction.lean)
-/
@[path]
private lemma bpc_dartNext_diff_singleton_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {e : Dart}
-- given
  (h : bpc_NotProbed c e) :
-- imply
  dartNext (K \ {c}) e = dartNext K e := by
-- proof
  apply StatMech.Lattice.bpc_dartNext_diff_singleton K c e h

/--
[bpc_turnZ_diff_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalancePreservingContraction.lean)
-/
@[path]
private lemma bpc_turnZ_diff_singleton_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {e : Dart}
-- given
  (h : bpc_NotProbed c e) :
-- imply
  turnZ (K \ {c}) e = turnZ K e := by
-- proof
  apply StatMech.Lattice.bpc_turnZ_diff_singleton K c e h

/--
[bpc_iterate_dartNext_diff_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalancePreservingContraction.lean)
-/
@[path]
private lemma bpc_iterate_dartNext_diff_singleton_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {e : Dart}
  {k : ℕ}
-- given
  (hnp : ∀ i, bpc_NotProbed c ((dartNext K)^[i] e)) :
-- imply
  (dartNext (K \ {c}))^[k] e = (dartNext K)^[k] e := by
-- proof
  apply StatMech.Lattice.bpc_iterate_dartNext_diff_singleton K c e hnp k

/--
[bpc_isBoundaryDart_diff_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalancePreservingContraction.lean)
-/
@[path]
private lemma bpc_isBoundaryDart_diff_singleton_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hc : c ≠ e.tail) :
-- imply
  IsBoundaryDart (K \ {c}) e := by
-- proof
  apply StatMech.Lattice.bpc_isBoundaryDart_diff_singleton K c e he hc

/--
[bpc_isPeriodicPt_diff_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalancePreservingContraction.lean)
-/
@[path]
private lemma bpc_isPeriodicPt_diff_singleton_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {a : {e : Dart // IsBoundaryDart K e}}
  {a' : {e : Dart // IsBoundaryDart (K \ {c}) e}}
  {n : ℕ}
-- given
  (hval : a'.1 = a.1)
  (hnp : ∀ i, bpc_NotProbed c ((dartNext K)^[i] a.1)) :
-- imply
  Function.IsPeriodicPt (dartNextSub (K \ {c})) n a' ↔ Function.IsPeriodicPt (dartNextSub K) n a := by
-- proof
  apply StatMech.Lattice.bpc_isPeriodicPt_diff_singleton K c a a' hval hnp n

/--
[bpc_dartOrbitPeriod_diff_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalancePreservingContraction.lean)
-/
@[path]
private lemma bpc_dartOrbitPeriod_diff_singleton_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {a : {e : Dart // IsBoundaryDart K e}}
  {a' : {e : Dart // IsBoundaryDart (K \ {c}) e}}
-- given
  (hval : a'.1 = a.1)
  (hnp : ∀ i, bpc_NotProbed c ((dartNext K)^[i] a.1)) :
-- imply
  dartOrbitPeriod (K \ {c}) a' = dartOrbitPeriod K a := by
-- proof
  apply StatMech.Lattice.bpc_dartOrbitPeriod_diff_singleton K c a a' hval hnp

/--
[bpc_cornerBalance_diff_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalancePreservingContraction.lean)
-/
@[path]
private lemma bpc_cornerBalance_diff_singleton_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {a : {e : Dart // IsBoundaryDart K e}}
  {a' : {e : Dart // IsBoundaryDart (K \ {c}) e}}
-- given
  (hval : a'.1 = a.1)
  (hnp : ∀ i, bpc_NotProbed c ((dartNext K)^[i] a.1)) :
-- imply
  cornerBalance (K \ {c}) a' = cornerBalance K a := by
-- proof
  apply StatMech.Lattice.bpc_cornerBalance_diff_singleton K c a a' hval hnp

/--
[bpc_notProbed_of_not_footprint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalancePreservingContraction.lean)
-/
@[path]
private lemma bpc_notProbed_of_not_footprint_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {c : Site 2}
  {i : ℕ}
-- given
  (hc : c ∉ bpc_orbitFootprint K a) :
-- imply
  bpc_NotProbed c ((dartNext K)^[i] a.1) := by
-- proof
  apply StatMech.Lattice.bpc_notProbed_of_not_footprint K a c hc i

/--
[bpc_ne_tail_of_not_footprint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalancePreservingContraction.lean)
-/
@[path]
private lemma bpc_ne_tail_of_not_footprint_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {c : Site 2}
-- given
  (hc : c ∉ bpc_orbitFootprint K a) :
-- imply
  c ≠ a.1.tail := by
-- proof
  apply StatMech.Lattice.bpc_ne_tail_of_not_footprint K a c hc

/--
[bpc_contraction_of_not_saturating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalancePreservingContraction.lean)
-/
@[path]
private lemma bpc_contraction_of_not_saturating_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {c : Site 2}
-- given
  (hK : K.Finite)
  (hcK : c ∈ K)
  (hc : c ∉ bpc_orbitFootprint K a) :
-- imply
  ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty) (a' : {e : Dart // IsBoundaryDart K' e}), K'.ncard < K.ncard ∧ cornerBalance K' a' = cornerBalance K a := by
-- proof
  apply StatMech.Lattice.bpc_contraction_of_not_saturating K hK a c hcK hc

/--
[bpc_balancePreservingContraction_of_saturating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalancePreservingContraction.lean)
-/
@[path]
private lemma bpc_balancePreservingContraction_of_saturating_eq
-- given
  (h : bpc_BalanceSaturatingContraction) :
-- imply
  BalancePreservingContraction := by
-- proof
  apply StatMech.Lattice.bpc_balancePreservingContraction_of_saturating h

/--
[bpc_totalTurn_eq_four_of_saturating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalancePreservingContraction.lean)
-/
@[path]
private lemma bpc_totalTurn_eq_four_of_saturating_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hSK : (ndt_StarHull K).Finite)
  (hne : (ndt_StarHull K).Nonempty)
  (hsat : bpc_BalanceSaturatingContraction) :
-- imply
  TurningIsFullRevolution (ndt_StarHull K) a := by
-- proof
  apply StatMech.Lattice.bpc_totalTurn_eq_four_of_saturating K hSK hne a hsat

/--
[bpc_totalTurn_eq_four_value_of_saturating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalancePreservingContraction.lean)
-/
@[path]
private lemma bpc_totalTurn_eq_four_value_of_saturating_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hSK : (ndt_StarHull K).Finite)
  (hne : (ndt_StarHull K).Nonempty)
  (hsat : bpc_BalanceSaturatingContraction) :
-- imply
  totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨ totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 := by
-- proof
  apply StatMech.Lattice.bpc_totalTurn_eq_four_value_of_saturating K hSK hne a hsat

/--
[bpc_domino_cornerBalance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalancePreservingContraction.lean)
-/
@[path]
private lemma bpc_domino_cornerBalance_eq :
-- imply
  cornerBalance domino dmBase = -4 := by
-- proof
  apply StatMech.Lattice.bpc_domino_cornerBalance

/--
[bpc_domino_diff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalancePreservingContraction.lean)
-/
@[path]
private lemma bpc_domino_diff_eq :
-- imply
  domino \ {(![1, 0] : Site 2)} = unitCell := by
-- proof
  apply StatMech.Lattice.bpc_domino_diff

/--
[bpc_domino_balanceSaturatingContraction_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalancePreservingContraction.lean)
-/
@[path]
private lemma bpc_domino_balanceSaturatingContraction_witness_eq :
-- imply
  ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty) (a' : {e : Dart // IsBoundaryDart K' e}), K'.ncard < domino.ncard ∧ cornerBalance K' a' = cornerBalance domino dmBase := by
-- proof
  apply StatMech.Lattice.bpc_domino_balanceSaturatingContraction_witness


-- created on 2026-10-23
