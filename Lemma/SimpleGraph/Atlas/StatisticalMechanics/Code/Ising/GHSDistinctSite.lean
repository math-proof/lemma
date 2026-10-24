import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.GHSDistinctSite
open Finset SimpleGraph Set StatMech StatMech.Ising


/--
[ghsQFactor_single_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDistinctSite.lean)
-/
@[path]
private lemma ghsQFactor_single_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {B : Finset V}
  {q : ConfigSpace V} :
-- imply
  0 ≤ 1 - spinProd B q := by
-- proof
  apply StatMech.Ising.ghsQFactor_single_nonneg B q

/--
[dup_single_pairing_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDistinctSite.lean)
-/
@[path]
private lemma dup_single_pairing_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A B : Finset V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  isingExpectation G β h (spinProd A) * isingExpectation G β h (spinProd B) ≤ isingExpectation G β h (spinProd (A ∆ B)) := by
-- proof
  apply StatMech.Ising.dup_single_pairing_nonneg G β h hβ hh A B

/--
[ghsQFactor_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDistinctSite.lean)
-/
@[path]
private lemma ghsQFactor_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ConfigSpace V}
  {o x y : V} :
-- imply
  ghsQFactor q o x y = 1 - spin q x * spin q y - spin q o * spin q y - spin q o * spin q x := by
-- proof
  apply StatMech.Ising.ghsQFactor_eq G q o x y

/--
[ghsQFactor_const_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDistinctSite.lean)
-/
@[path]
private lemma ghsQFactor_const_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V} :
-- imply
  ghsQFactor (fun _ => true) o x y = -2 := by
-- proof
  apply StatMech.Ising.ghsQFactor_const_one G o x y

/--
[ghsQFactor_single_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDistinctSite.lean)
-/
@[path]
private lemma ghsQFactor_single_flip_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hxy : x ≠ y) :
-- imply
  ghsQFactor (fun z => decide (z ≠ x)) o x y = 2 := by
-- proof
  apply StatMech.Ising.ghsQFactor_single_flip G hox hxy

/--
[ghsQFactor_not_signDefinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDistinctSite.lean)
-/
@[path]
private lemma ghsQFactor_not_signDefinite_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hxy : x ≠ y) :
-- imply
  (∃ q : ConfigSpace V, ghsQFactor q o x y < 0) ∧ (∃ q : ConfigSpace V, 0 < ghsQFactor q o x y) := by
-- proof
  apply StatMech.Ising.ghsQFactor_not_signDefinite G hox hxy

/--
[dup_signDefinite_iff_single](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDistinctSite.lean)
-/
@[path]
private lemma dup_signDefinite_iff_single_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {B : Finset V}
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hxy : x ≠ y) :
-- imply
  (∀ q : ConfigSpace V, 0 ≤ 1 - spinProd B q) ∧ ¬ (∀ q : ConfigSpace V, 0 ≤ ghsQFactor q o x y) := by
-- proof
  apply StatMech.Ising.dup_signDefinite_iff_single G B hox hxy


-- created on 2026-10-23
