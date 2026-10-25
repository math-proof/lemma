import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc5_firstreturn
open SimpleGraph Function StatMech StatMech.Walls


/--
[jc5_firstReturn_isLeastFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_firstreturn.lean)
-/
@[path]
private lemma jc5_firstReturn_isLeastFree_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i) :
-- imply
  1 ≤ jc4_firstReturnK K a r hex ∧ jc4_FootprintFree K a r (jc4_firstReturnK K a r hex) ∧ (∀ k, 1 ≤ k → jc4_FootprintFree K a r k → jc4_firstReturnK K a r hex ≤ k) := by
-- proof
  apply StatMech.Walls.jc5_firstReturn_isLeastFree K a r hex

/--
[jc5_firstReturn_touching_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_firstreturn.lean)
-/
@[path]
private lemma jc5_firstReturn_touching_lt_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {k : ℕ}
-- given
  (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
  (ha0 : ¬ jc4_FootprintFree K a r 0)
  (hk : k < jc4_firstReturnK K a r hex) :
-- imply
  ¬ jc4_FootprintFree K a r k := by
-- proof
  apply StatMech.Walls.jc5_firstReturn_touching_lt K a r hex ha0 k hk

/--
[jc5_firstReturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_firstreturn.lean)
-/
@[path]
private lemma jc5_firstReturn_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
  (ha0 : ¬ jc4_FootprintFree K a r 0) :
-- imply
  (1 ≤ jc4_firstReturnK K a r hex ∧ jc4_FootprintFree K a r (jc4_firstReturnK K a r hex) ∧ (∀ k, 1 ≤ k → jc4_FootprintFree K a r k → jc4_firstReturnK K a r hex ≤ k)) ∧ (∀ k, k < jc4_firstReturnK K a r hex → ¬ jc4_FootprintFree K a r k) := by
-- proof
  apply StatMech.Walls.jc5_firstReturn K a r hex ha0

/--
[jc5_firstReturn_within_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_firstreturn.lean)
-/
@[path]
private lemma jc5_firstReturn_within_cycle_eq
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
  apply StatMech.Walls.jc5_firstReturn_within_cycle K hK a r hex ha0

/--
[jc5_firstReturn_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_firstreturn.lean)
-/
@[path]
private lemma jc5_firstReturn_unique_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {n : ℕ}
-- given
  (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
  (hn1 : 1 ≤ n)
  (hnfree : jc4_FootprintFree K a r n)
  (hnleast : ∀ k, 1 ≤ k → jc4_FootprintFree K a r k → n ≤ k) :
-- imply
  n = jc4_firstReturnK K a r hex := by
-- proof
  apply StatMech.Walls.jc5_firstReturn_unique K a r hex n hn1 hnfree hnleast

/--
[jc5_firstReturn_of_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_firstreturn.lean)
-/
@[path]
private lemma jc5_firstReturn_of_witness_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {j : ℕ}
-- given
  (hK : K.Finite)
  (hj : jc4_FootprintFree K a r j)
  (ha0 : ¬ jc4_FootprintFree K a r 0) :
-- imply
  ∃ m : ℕ, (1 ≤ m ∧ jc4_FootprintFree K a r m ∧ (∀ k, 1 ≤ k → jc4_FootprintFree K a r k → m ≤ k)) ∧ (∀ k, k < m → ¬ jc4_FootprintFree K a r k) := by
-- proof
  apply StatMech.Walls.jc5_firstReturn_of_witness K hK a r j hj ha0

/--
[jc5_firstReturn_isLeastFree_of_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_firstreturn.lean)
-/
@[path]
private lemma jc5_firstReturn_isLeastFree_of_witness_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {j : ℕ}
-- given
  (hK : K.Finite)
  (hj : jc4_FootprintFree K a r j) :
-- imply
  ∃ (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i), 1 ≤ jc4_firstReturnK K a r hex ∧ jc4_FootprintFree K a r (jc4_firstReturnK K a r hex) ∧ (∀ k, 1 ≤ k → jc4_FootprintFree K a r k → jc4_firstReturnK K a r hex ≤ k) := by
-- proof
  apply StatMech.Walls.jc5_firstReturn_isLeastFree_of_witness K hK a r j hj

/--
[jc5_firstReturn_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_firstreturn.lean)
-/
@[path]
private lemma jc5_firstReturn_nonvacuous_eq
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
  apply StatMech.Walls.jc5_firstReturn_nonvacuous K hK a r j hj ha0

/--
[jc5_firstReturn_tailStart_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_firstreturn.lean)
-/
@[path]
private lemma jc5_firstReturn_tailStart_free_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i) :
-- imply
  jc3_AvoidsEarFootprint r ((dartNext K)^[jc4_firstReturnK K a r hex + 0] a.1) := by
-- proof
  apply StatMech.Walls.jc5_firstReturn_tailStart_free K a r hex


-- created on 2026-10-23
