import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.jc2_core
open SimpleGraph Function Set StatMech StatMech.Walls


/--
[jc2_contraction_of_orbitMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_core.lean)
-/
@[path]
private lemma jc2_contraction_of_orbitMatch_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : jc2_OrbitMatchAt K a) :
-- imply
  ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty) (a' : {e : Dart // IsBoundaryDart K' e}), K'.ncard < K.ncard ∧ cornerBalance K' a' = cornerBalance K a := by
-- proof
  apply StatMech.Walls.jc2_contraction_of_orbitMatch K a h

/--
[jc2_orbitMatch_of_contraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_core.lean)
-/
@[path]
private lemma jc2_orbitMatch_of_contraction_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty) (a' : {e : Dart // IsBoundaryDart K' e}), K'.ncard < K.ncard ∧ cornerBalance K' a' = cornerBalance K a) :
-- imply
  jc2_OrbitMatchAt K a := by
-- proof
  apply StatMech.Walls.jc2_orbitMatch_of_contraction K a h

/--
[jc2_orbitMatch_iff_contraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_core.lean)
-/
@[path]
private lemma jc2_orbitMatch_iff_contraction_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  jc2_OrbitMatchAt K a ↔ ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty) (a' : {e : Dart // IsBoundaryDart K' e}), K'.ncard < K.ncard ∧ cornerBalance K' a' = cornerBalance K a := by
-- proof
  apply StatMech.Walls.jc2_orbitMatch_iff_contraction K a

/--
[jc2_pendantClip_card_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_core.lean)
-/
@[path]
private lemma jc2_pendantClip_card_lt_eq
  {K : Set (Site 2)}
  {r : Site 2}
-- given
  (hK : K.Finite)
  (hr : r ∈ K) :
-- imply
  (K \ {r}).ncard < K.ncard := by
-- proof
  apply StatMech.Walls.jc2_pendantClip_card_lt K hK r hr

/--
[jc2_contraction_of_pendantClipMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_core.lean)
-/
@[path]
private lemma jc2_contraction_of_pendantClipMatch_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hK : K.Finite)
  (hr : r ∈ K)
  (h : jc2_PendantClipMatch K a r) :
-- imply
  ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty) (a' : {e : Dart // IsBoundaryDart K' e}), K'.ncard < K.ncard ∧ cornerBalance K' a' = cornerBalance K a := by
-- proof
  apply StatMech.Walls.jc2_contraction_of_pendantClipMatch K hK a r hr h

/--
[jc2_balanceSaturatingContraction_of_earMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_core.lean)
-/
@[path]
private lemma jc2_balanceSaturatingContraction_of_earMatch_eq
-- given
  (h : jc2_SaturatingEarMatch) :
-- imply
  bpc_BalanceSaturatingContraction := by
-- proof
  apply StatMech.Walls.jc2_balanceSaturatingContraction_of_earMatch h

/--
[jc2_balancePreservingContraction_of_earMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_core.lean)
-/
@[path]
private lemma jc2_balancePreservingContraction_of_earMatch_eq
-- given
  (h : jc2_SaturatingEarMatch) :
-- imply
  BalancePreservingContraction := by
-- proof
  apply StatMech.Walls.jc2_balancePreservingContraction_of_earMatch h

/--
[jc2_turningIsFullRevolution_of_earMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_core.lean)
-/
@[path]
private lemma jc2_turningIsFullRevolution_of_earMatch_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : jc2_SaturatingEarMatch)
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  TurningIsFullRevolution K a := by
-- proof
  apply StatMech.Walls.jc2_turningIsFullRevolution_of_earMatch h K hK hne a

/--
[jc2_starHull_turningIsFullRevolution_of_earMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_core.lean)
-/
@[path]
private lemma jc2_starHull_turningIsFullRevolution_of_earMatch_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (h : jc2_SaturatingEarMatch)
  (hSK : (ndt_StarHull K).Finite)
  (hne : (ndt_StarHull K).Nonempty) :
-- imply
  TurningIsFullRevolution (ndt_StarHull K) a := by
-- proof
  apply StatMech.Walls.jc2_starHull_turningIsFullRevolution_of_earMatch h K hSK hne a

/--
[jc2_starHull_totalTurn_eq_four_of_earMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_core.lean)
-/
@[path]
private lemma jc2_starHull_totalTurn_eq_four_of_earMatch_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (h : jc2_SaturatingEarMatch)
  (hSK : (ndt_StarHull K).Finite)
  (hne : (ndt_StarHull K).Nonempty) :
-- imply
  totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨ totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 := by
-- proof
  apply StatMech.Walls.jc2_starHull_totalTurn_eq_four_of_earMatch h K hSK hne a

/--
[jc2_saturating_has_runFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_core.lean)
-/
@[path]
private lemma jc2_saturating_has_runFrame_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hge : 2 ≤ K.ncard) :
-- imply
  ∃ c len, jc2_RunFrame K c len := by
-- proof
  apply StatMech.Walls.jc2_saturating_has_runFrame K hK hge

/--
[jc2_runFrame_thinThickDichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_core.lean)
-/
@[path]
private lemma jc2_runFrame_thinThickDichotomy_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hframe : jc2_RunFrame K c len) :
-- imply
  jc2_ThinThickDichotomy K c len := by
-- proof
  apply StatMech.Walls.jc2_runFrame_thinThickDichotomy K c len hframe

/--
[jc2_thin_book_ear_cellConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_core.lean)
-/
@[path]
private lemma jc2_thin_book_ear_cellConnected_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hconn : CellConnected K)
  (hframe : jc2_RunFrame K c len)
  (hlen : 1 ≤ len)
  (hthin : (c + ![len, 0] : Site 2) + ![0, -1] ∉ K) :
-- imply
  CellConnected (K \ {(c + ![len, 0] : Site 2)}) := by
-- proof
  apply StatMech.Walls.jc2_thin_book_ear_cellConnected K c len hconn hframe hlen hthin

/--
[jc2_unitCell_core_balanceIsFour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_core.lean)
-/
@[path]
private lemma jc2_unitCell_core_balanceIsFour_eq :
-- imply
  BalanceIsFour unitCell ucBase := by
-- proof
  apply StatMech.Walls.jc2_unitCell_core_balanceIsFour

/--
[jc2_domino_core_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_core.lean)
-/
@[path]
private lemma jc2_domino_core_witness_eq :
-- imply
  ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty) (a' : {e : Dart // IsBoundaryDart K' e}), K'.ncard < domino.ncard ∧ cornerBalance K' a' = cornerBalance domino dmBase := by
-- proof
  apply StatMech.Walls.jc2_domino_core_witness

/--
[jc2_domino_book_ear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_core.lean)
-/
@[path]
private lemma jc2_domino_book_ear_eq :
-- imply
  jc2_RunFrame domino (![0, 0] : Site 2) 1 := by
-- proof
  apply StatMech.Walls.jc2_domino_book_ear

/--
[jc2_domino_thin_book_ear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_core.lean)
-/
@[path]
private lemma jc2_domino_thin_book_ear_eq :
-- imply
  jc_IsPendantCell domino ((![0, 0] : Site 2) + ![1, 0]) := by
-- proof
  apply StatMech.Walls.jc2_domino_thin_book_ear


-- created on 2026-10-23
