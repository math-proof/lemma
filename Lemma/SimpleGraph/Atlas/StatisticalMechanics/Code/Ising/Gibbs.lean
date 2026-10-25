import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
open Finset StatMech StatMech.Ising


/--
[spin_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Gibbs.lean)
-/
@[path]
private lemma spin_true_eq
  {s : ConfigSpace V}
  {x : V}
-- given
  (hx : s x = true) :
-- imply
  spin s x = 1 := by
-- proof
  apply StatMech.Ising.spin_true s hx

/--
[spin_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Gibbs.lean)
-/
@[path]
private lemma spin_false_eq
  {s : ConfigSpace V}
  {x : V}
-- given
  (hx : s x = false) :
-- imply
  spin s x = -1 := by
-- proof
  apply StatMech.Ising.spin_false s hx

/--
[spin_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Gibbs.lean)
-/
@[path]
private lemma spin_sq_eq
  {s : ConfigSpace V}
  {x : V} :
-- imply
  spin s x * spin s x = 1 := by
-- proof
  apply StatMech.Ising.spin_sq s x

/--
[abs_spin_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Gibbs.lean)
-/
@[path]
private lemma abs_spin_le_one_eq
  {s : ConfigSpace V}
  {x : V} :
-- imply
  |spin s x| ≤ 1 := by
-- proof
  apply StatMech.Ising.abs_spin_le_one s x

/--
[bond_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Gibbs.lean)
-/
@[path]
private lemma bond_mk_eq
  {s : ConfigSpace V}
  {x y : V} :
-- imply
  bond s s(x, y) = spin s x * spin s y := by
-- proof
  apply StatMech.Ising.bond_mk s x y

/--
[isingWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Gibbs.lean)
-/
@[path]
private lemma isingWeight_pos_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V}
-- given
  (β h : ℝ) :
-- imply
  0 < isingWeight G β h s := by
-- proof
  apply StatMech.Ising.isingWeight_pos β h s

/--
[isingWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Gibbs.lean)
-/
@[path]
private lemma isingWeight_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V}
-- given
  (β h : ℝ) :
-- imply
  0 ≤ isingWeight G β h s := by
-- proof
  apply StatMech.Ising.isingWeight_nonneg β h s

/--
[isingZ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Gibbs.lean)
-/
@[path]
private lemma isingZ_pos_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (β h : ℝ) :
-- imply
  0 < isingZ G β h := by
-- proof
  apply StatMech.Ising.isingZ_pos β h

/--
[isingZ_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Gibbs.lean)
-/
@[path]
private lemma isingZ_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (β h : ℝ) :
-- imply
  isingZ G β h ≠ 0 := by
-- proof
  apply StatMech.Ising.isingZ_ne_zero β h

/--
[isingProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Gibbs.lean)
-/
@[path]
private lemma isingProb_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V}
-- given
  (β h : ℝ) :
-- imply
  0 ≤ isingProb G β h s := by
-- proof
  apply StatMech.Ising.isingProb_nonneg β h s

/--
[isingProb_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Gibbs.lean)
-/
@[path]
private lemma isingProb_pos_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V}
-- given
  (β h : ℝ) :
-- imply
  0 < isingProb G β h s := by
-- proof
  apply StatMech.Ising.isingProb_pos β h s

/--
[isingProb_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Gibbs.lean)
-/
@[path]
private lemma isingProb_sum_eq_one_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (β h : ℝ) :
-- imply
  ∑ s : ConfigSpace V, isingProb G β h s = 1 := by
-- proof
  apply StatMech.Ising.isingProb_sum_eq_one β h

/--
[isingPMF_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Gibbs.lean)
-/
@[path]
private lemma isingPMF_apply_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V}
-- given
  (β h : ℝ) :
-- imply
  isingPMF G β h s = ENNReal.ofReal (isingProb G β h s) := by
-- proof
  apply StatMech.Ising.isingPMF_apply β h s


-- created on 2026-10-23
