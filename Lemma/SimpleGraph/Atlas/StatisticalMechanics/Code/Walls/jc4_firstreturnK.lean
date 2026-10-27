import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc4_firstreturnK.Part2
open SimpleGraph Function StatMech StatMech.Walls


/--
[jc4_iterate_period_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_firstreturnK.lean)
-/
@[path]
private lemma jc4_iterate_period_eq_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (dartNext K)^[dartOrbitPeriod K a] a.1 = a.1 := by
-- proof
  apply StatMech.Walls.jc4_iterate_period_eq K a

/--
[jc4_firstReturn_exists_of_some_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_firstreturnK.lean)
-/
@[path]
private lemma jc4_firstReturn_exists_of_some_free_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {j : ℕ}
-- given
  (hK : K.Finite)
  (hj : jc4_FootprintFree K a r j) :
-- imply
  ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i := by
-- proof
  apply StatMech.Walls.jc4_firstReturn_exists_of_some_free K hK a r j hj

/--
[jc4_firstReturnK_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_firstreturnK.lean)
-/
@[path]
private lemma jc4_firstReturnK_pos_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i) :
-- imply
  1 ≤ jc4_firstReturnK K a r hex := by
-- proof
  apply StatMech.Walls.jc4_firstReturnK_pos K a r hex

/--
[jc4_firstReturnK_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_firstreturnK.lean)
-/
@[path]
private lemma jc4_firstReturnK_free_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i) :
-- imply
  jc4_FootprintFree K a r (jc4_firstReturnK K a r hex) := by
-- proof
  apply StatMech.Walls.jc4_firstReturnK_free K a r hex

/--
[jc4_firstReturnK_avoidsEarFootprint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_firstreturnK.lean)
-/
@[path]
private lemma jc4_firstReturnK_avoidsEarFootprint_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i) :
-- imply
  jc3_AvoidsEarFootprint r ((dartNext K)^[jc4_firstReturnK K a r hex] a.1) := by
-- proof
  apply StatMech.Walls.jc4_firstReturnK_avoidsEarFootprint K a r hex

/--
[jc4_firstReturnK_lt_touching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_firstreturnK.lean)
-/
@[path]
private lemma jc4_firstReturnK_lt_touching_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {k : ℕ}
-- given
  (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
  (hk1 : 1 ≤ k)
  (hk : k < jc4_firstReturnK K a r hex) :
-- imply
  ¬ jc4_FootprintFree K a r k := by
-- proof
  apply StatMech.Walls.jc4_firstReturnK_lt_touching K a r hex k hk1 hk

/--
[jc4_firstReturnK_maximalInitialBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_firstreturnK.lean)
-/
@[path]
private lemma jc4_firstReturnK_maximalInitialBlock_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
  (ha0 : ¬ jc4_FootprintFree K a r 0) :
-- imply
  1 ≤ jc4_firstReturnK K a r hex ∧ jc4_FootprintFree K a r (jc4_firstReturnK K a r hex) ∧ (∀ k, k < jc4_firstReturnK K a r hex → ¬ jc4_FootprintFree K a r k) := by
-- proof
  apply StatMech.Walls.jc4_firstReturnK_maximalInitialBlock K a r hex ha0

/--
[jc4_firstReturnK_le_of_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_firstreturnK.lean)
-/
@[path]
private lemma jc4_firstReturnK_le_of_witness_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {j : ℕ}
-- given
  (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
  (hj1 : 1 ≤ j)
  (hj : jc4_FootprintFree K a r j) :
-- imply
  jc4_firstReturnK K a r hex ≤ j := by
-- proof
  apply StatMech.Walls.jc4_firstReturnK_le_of_witness K a r hex j hj1 hj

/--
[jc4_firstReturnK_le_period_of_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_firstreturnK.lean)
-/
@[path]
private lemma jc4_firstReturnK_le_period_of_free_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hK : K.Finite)
  (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
  (ha0 : jc4_FootprintFree K a r 0) :
-- imply
  jc4_firstReturnK K a r hex ≤ dartOrbitPeriod K a := by
-- proof
  apply StatMech.Walls.jc4_firstReturnK_le_period_of_free K hK a r hex ha0

/--
[jc4_firstReturnK_remains_free_of_initialBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_firstreturnK.lean)
-/
@[path]
private lemma jc4_firstReturnK_remains_free_of_initialBlock_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {i : ℕ}
-- given
  (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
  (hinit : ∀ i, i < dartOrbitPeriod K a → ¬ jc4_FootprintFree K a r i → ∀ k, k ≤ i → ¬ jc4_FootprintFree K a r k)
  (hmi : jc4_firstReturnK K a r hex ≤ i)
  (hip : i < dartOrbitPeriod K a) :
-- imply
  jc4_FootprintFree K a r i := by
-- proof
  apply StatMech.Walls.jc4_firstReturnK_remains_free_of_initialBlock K a r hex hinit i hmi hip

/--
[jc4_firstReturnK_of_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_firstreturnK.lean)
-/
@[path]
private lemma jc4_firstReturnK_of_witness_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {j : ℕ}
-- given
  (hK : K.Finite)
  (hj : jc4_FootprintFree K a r j)
  (ha0 : ¬ jc4_FootprintFree K a r 0) :
-- imply
  ∃ m : ℕ, 1 ≤ m ∧ jc4_FootprintFree K a r m ∧ (∀ k, k < m → ¬ jc4_FootprintFree K a r k) := by
-- proof
  apply StatMech.Walls.jc4_firstReturnK_of_witness K hK a r j hj ha0

/--
[jc4_firstReturnK_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_firstreturnK.lean)
-/
@[path]
private lemma jc4_firstReturnK_nonvacuous_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {j : ℕ}
-- given
  (hK : K.Finite)
  (hj : jc4_FootprintFree K a r j) :
-- imply
  ∃ (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i), 1 ≤ jc4_firstReturnK K a r hex := by
-- proof
  apply StatMech.Walls.jc4_firstReturnK_nonvacuous K hK a r j hj


-- created on 2026-10-23
