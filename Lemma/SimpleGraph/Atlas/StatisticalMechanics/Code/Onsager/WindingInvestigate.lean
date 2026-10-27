import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.WindingInvestigate
open SimpleGraph Function Set StatMech StatMech.Lattice


/--
[wi_totalTurn_eq_four_of_winds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingInvestigate.lean)
-/
@[path]
private lemma wi_totalTurn_eq_four_of_winds_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hmax : |totalTurnZ K a.1 (dartOrbitPeriod K a)| ≤ 4)
  (hmin : totalTurnZ K a.1 (dartOrbitPeriod K a) ≠ 0) :
-- imply
  totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 ∨ totalTurnZ K a.1 (dartOrbitPeriod K a) = -4 := by
-- proof
  apply StatMech.Lattice.wi_totalTurn_eq_four_of_winds K a hmax hmin

/--
[wi_winds_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingInvestigate.lean)
-/
@[path]
private lemma wi_winds_iff_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (|totalTurnZ K a.1 (dartOrbitPeriod K a)| ≤ 4 ∧ totalTurnZ K a.1 (dartOrbitPeriod K a) ≠ 0) ↔ TurningIsFullRevolution K a := by
-- proof
  apply StatMech.Lattice.wi_winds_iff K a

/--
[wi_turningIsFullRevolution_of_saturating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingInvestigate.lean)
-/
@[path]
private lemma wi_turningIsFullRevolution_of_saturating_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hsat : bpc_BalanceSaturatingContraction)
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  TurningIsFullRevolution K a := by
-- proof
  apply StatMech.Lattice.wi_turningIsFullRevolution_of_saturating hsat K hK hne a

/--
[wi_totalTurn_eq_four_of_saturating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingInvestigate.lean)
-/
@[path]
private lemma wi_totalTurn_eq_four_of_saturating_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hsat : bpc_BalanceSaturatingContraction)
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 ∨ totalTurnZ K a.1 (dartOrbitPeriod K a) = -4 := by
-- proof
  apply StatMech.Lattice.wi_totalTurn_eq_four_of_saturating hsat K hK hne a

/--
[wi_winds_of_saturating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingInvestigate.lean)
-/
@[path]
private lemma wi_winds_of_saturating_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hsat : bpc_BalanceSaturatingContraction)
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  |totalTurnZ K a.1 (dartOrbitPeriod K a)| ≤ 4 ∧ totalTurnZ K a.1 (dartOrbitPeriod K a) ≠ 0 := by
-- proof
  apply StatMech.Lattice.wi_winds_of_saturating hsat K hK hne a

/--
[wi_eulerCharOne_of_saturating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingInvestigate.lean)
-/
@[path]
private lemma wi_eulerCharOne_of_saturating_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hsat : bpc_BalanceSaturatingContraction)
  (hK : K.Finite)
  (hne : K.Nonempty)
  (hp : 3 ≤ dartOrbitPeriod K a) :
-- imply
  EulerCharOne K a := by
-- proof
  apply StatMech.Lattice.wi_eulerCharOne_of_saturating hsat K hK hne a hp

/--
[wi_ttf_winds_of_saturating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingInvestigate.lean)
-/
@[path]
private lemma wi_ttf_winds_of_saturating_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hsat : bpc_BalanceSaturatingContraction)
  (hSK : (ndt_StarHull K).Finite)
  (hne : (ndt_StarHull K).Nonempty) :
-- imply
  ttf_WindsAtMostOnce K a ∧ ttf_WindsAtLeastOnce K a := by
-- proof
  apply StatMech.Lattice.wi_ttf_winds_of_saturating hsat K hSK hne a

/--
[wi_residue_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingInvestigate.lean)
-/
@[path]
private lemma wi_residue_chain_eq
-- given
  (hsat : bpc_BalanceSaturatingContraction) :
-- imply
  BalancePreservingContraction := by
-- proof
  apply StatMech.Lattice.wi_residue_chain hsat

/--
[wi_domino_saturating_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingInvestigate.lean)
-/
@[path]
private lemma wi_domino_saturating_witness_eq :
-- imply
  ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty) (a' : {e : Dart // IsBoundaryDart K' e}), K'.ncard < domino.ncard ∧ cornerBalance K' a' = cornerBalance domino dmBase := by
-- proof
  apply StatMech.Lattice.wi_domino_saturating_witness


-- created on 2026-10-23
