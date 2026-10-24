import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.GaussBonnetEar
open SimpleGraph Function Set Finset StatMech StatMech.Lattice


/--
[gbe_faceLabel_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnetEar.lean)
-/
@[path]
private lemma gbe_faceLabel_injOn_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hmult : usc_FaceMultiplicityOne K a) :
-- imply
  Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a)) := by
-- proof
  apply StatMech.Lattice.gbe_faceLabel_injOn K a hmult

/--
[gbe_orbitFaces_card_eq_period](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnetEar.lean)
-/
@[path]
private lemma gbe_orbitFaces_card_eq_period_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hmult : usc_FaceMultiplicityOne K a) :
-- imply
  (usc_orbitFaces K a).card = dartOrbitPeriod K a := by
-- proof
  apply StatMech.Lattice.gbe_orbitFaces_card_eq_period K a hmult

/--
[gbe_starHull_orbitFaces_card_eq_period](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnetEar.lean)
-/
@[path]
private lemma gbe_starHull_orbitFaces_card_eq_period_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}} :
-- imply
  (usc_orbitFaces (ndt_StarHull K) a).card = dartOrbitPeriod (ndt_StarHull K) a := by
-- proof
  apply StatMech.Lattice.gbe_starHull_orbitFaces_card_eq_period K a

/--
[gbe_ear_first_turn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnetEar.lean)
-/
@[path]
private lemma gbe_ear_first_turn_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : IsExtremeCell K c) :
-- imply
  turnZ K ((dartNext K)^[0] (leftDart c)) = -1 := by
-- proof
  apply StatMech.Lattice.gbe_ear_first_turn K c hc

/--
[gbe_exists_convex_ear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnetEar.lean)
-/
@[path]
private lemma gbe_exists_convex_ear_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  ∃ e : Dart, IsBoundaryDart K e ∧ turnZ K e = -1 := by
-- proof
  apply StatMech.Lattice.gbe_exists_convex_ear K hK hne

/--
[gbe_ear_step_preserves_turn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnetEar.lean)
-/
@[path]
private lemma gbe_ear_step_preserves_turn_eq
  {K K' : Set (Site 2)}
  {e e' : Dart}
  {m m' n : ℕ}
-- given
  (hmatch : ∀ i, i < n → turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
  (hbal : umEar_windowTurn K' e' 0 m' = umEar_windowTurn K e 0 m) :
-- imply
  totalTurnZ K' e' (m' + n) = totalTurnZ K e (m + n) := by
-- proof
  apply StatMech.Lattice.gbe_ear_step_preserves_turn K K' e e' m m' n hmatch hbal

/--
[gbe_ear_step_preserves_turn_balance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnetEar.lean)
-/
@[path]
private lemma gbe_ear_step_preserves_turn_balance_eq
  {K K' : Set (Site 2)}
  {e e' : Dart}
  {m m' n : ℕ}
-- given
  (hmatch : ∀ i, i < n → turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
  (hbal : umEar_windowRight K' e' 0 m' - umEar_windowLeft K' e' 0 m' = umEar_windowRight K e 0 m - umEar_windowLeft K e 0 m) :
-- imply
  totalTurnZ K' e' (m' + n) = totalTurnZ K e (m + n) := by
-- proof
  apply StatMech.Lattice.gbe_ear_step_preserves_turn_balance K K' e e' m m' n hmatch hbal

/--
[gbe_singleton_totalTurn_eq_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnetEar.lean)
-/
@[path]
private lemma gbe_singleton_totalTurn_eq_four_eq
  {v : Site 2}
  {a : {e : Dart // IsBoundaryDart ({v} : Set (Site 2)) e}} :
-- imply
  totalTurnZ ({v} : Set (Site 2)) a.1 (dartOrbitPeriod ({v} : Set (Site 2)) a) = 4 ∨ totalTurnZ ({v} : Set (Site 2)) a.1 (dartOrbitPeriod ({v} : Set (Site 2)) a) = -4 := by
-- proof
  apply StatMech.Lattice.gbe_singleton_totalTurn_eq_four v a

/--
[gbe_totalTurn_eq_four_of_contraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnetEar.lean)
-/
@[path]
private lemma gbe_totalTurn_eq_four_of_contraction_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hSK : (ndt_StarHull K).Finite)
  (hne : (ndt_StarHull K).Nonempty)
  (hcontr : BalancePreservingContraction) :
-- imply
  TurningIsFullRevolution (ndt_StarHull K) a := by
-- proof
  apply StatMech.Lattice.gbe_totalTurn_eq_four_of_contraction K hSK hne a hcontr

/--
[gbe_totalTurn_eq_four_value_of_contraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnetEar.lean)
-/
@[path]
private lemma gbe_totalTurn_eq_four_value_of_contraction_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hSK : (ndt_StarHull K).Finite)
  (hne : (ndt_StarHull K).Nonempty)
  (hcontr : BalancePreservingContraction) :
-- imply
  totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨ totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 := by
-- proof
  apply StatMech.Lattice.gbe_totalTurn_eq_four_value_of_contraction K hSK hne a hcontr

/--
[gbe_starHull_exists_convex_corner_of_contraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnetEar.lean)
-/
@[path]
private lemma gbe_starHull_exists_convex_corner_of_contraction_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hSK : (ndt_StarHull K).Finite)
  (hne : (ndt_StarHull K).Nonempty)
  (hcontr : BalancePreservingContraction) :
-- imply
  (∃ f ∈ usc_orbitFaces (ndt_StarHull K) a, usc_localTurn (ndt_StarHull K) a f = 1) ∨ (∃ f ∈ usc_orbitFaces (ndt_StarHull K) a, usc_localTurn (ndt_StarHull K) a f = -1) := by
-- proof
  apply StatMech.Lattice.gbe_starHull_exists_convex_corner_of_contraction K hSK hne a hcontr

/--
[gbe_unitCell_totalTurn_eq_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnetEar.lean)
-/
@[path]
private lemma gbe_unitCell_totalTurn_eq_four_eq :
-- imply
  totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = 4 ∨ totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = -4 := by
-- proof
  apply StatMech.Lattice.gbe_unitCell_totalTurn_eq_four

/--
[gbe_domino_totalTurn_eq_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnetEar.lean)
-/
@[path]
private lemma gbe_domino_totalTurn_eq_four_eq :
-- imply
  totalTurnZ domino dmBase.1 (dartOrbitPeriod domino dmBase) = 4 ∨ totalTurnZ domino dmBase.1 (dartOrbitPeriod domino dmBase) = -4 := by
-- proof
  apply StatMech.Lattice.gbe_domino_totalTurn_eq_four

/--
[gbe_unitCell_balanceIsFour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnetEar.lean)
-/
@[path]
private lemma gbe_unitCell_balanceIsFour_eq :
-- imply
  BalanceIsFour unitCell ucBase := by
-- proof
  apply StatMech.Lattice.gbe_unitCell_balanceIsFour


-- created on 2026-10-23
