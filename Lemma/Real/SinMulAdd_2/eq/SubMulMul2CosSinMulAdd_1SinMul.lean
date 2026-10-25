import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.DihedralPositivityFinite
open Finset BigOperators CoxeterGroup


/--
[sin_chebyshev_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralPositivityFinite.lean)
-/
@[path]
private lemma sin_chebyshev_recurrence_eq
  [DecidableEq B]
  [Fintype B]
  {θ : ℝ}
  {n : ℕ} :
-- imply
  Real.sin (((n : ℝ) + 2) * θ) = 2 * Real.cos θ * Real.sin (((n : ℝ) + 1) * θ) - Real.sin ((n : ℝ) * θ) := by
-- proof
  apply CoxeterGroup.sin_chebyshev_recurrence θ n

/--
[formVal_eq_neg_cos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralPositivityFinite.lean)
-/
@[path]
private lemma formVal_eq_neg_cos_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
-- given
  (hm : M s t ≠ 0) :
-- imply
  formVal M s t = -Real.cos (Real.pi / (M s t : ℝ)) := by
-- proof
  apply CoxeterGroup.formVal_eq_neg_cos M s t hm

/--
[dihedral_coords_even_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralPositivityFinite.lean)
-/
@[path]
private lemma dihedral_coords_even_finite_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {k : ℕ}
-- given
  (hst : s ≠ t)
  (hm : M s t ≠ 0) :
-- imply
  let θ := Real.pi / (M s t : ℝ)
  wordSigma M (altWordEven s t k) (e s) s = Real.sin ((2 * (k : ℝ) + 1) * θ) / Real.sin θ ∧ wordSigma M (altWordEven s t k) (e s) t = Real.sin (2 * (k : ℝ) * θ) / Real.sin θ := by
-- proof
  apply CoxeterGroup.dihedral_coords_even_finite M s t hst hm k

/--
[dihedral_coords_odd_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralPositivityFinite.lean)
-/
@[path]
private lemma dihedral_coords_odd_finite_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {k : ℕ}
-- given
  (hst : s ≠ t)
  (hm : M s t ≠ 0) :
-- imply
  let θ := Real.pi / (M s t : ℝ)
  wordSigma M (t :: altWordEven s t k) (e s) s = Real.sin ((2 * (k : ℝ) + 1) * θ) / Real.sin θ ∧ wordSigma M (t :: altWordEven s t k) (e s) t = Real.sin ((2 * (k : ℝ) + 2) * θ) / Real.sin θ := by
-- proof
  apply CoxeterGroup.dihedral_coords_odd_finite M s t hst hm k

/--
[sin_nonneg_of_nat_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralPositivityFinite.lean)
-/
@[path]
private lemma sin_nonneg_of_nat_le_eq
  [DecidableEq B]
  [Fintype B]
  {m n : ℕ}
-- given
  (hm : m ≠ 0)
  (hn_le : n ≤ m) :
-- imply
  0 ≤ Real.sin ((n : ℝ) * (Real.pi / (m : ℝ))) := by
-- proof
  apply CoxeterGroup.sin_nonneg_of_nat_le m n hm hn_le

/--
[dihedral_pos_even_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralPositivityFinite.lean)
-/
@[path]
private lemma dihedral_pos_even_finite_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {k : ℕ}
-- given
  (hst : s ≠ t)
  (hm : M s t ≠ 0)
  (hk : 2 * k < M s t) :
-- imply
  IsPositive (wordSigma M (altWordEven s t k) (e s)) := by
-- proof
  apply CoxeterGroup.dihedral_pos_even_finite M s t hst hm k hk

/--
[dihedral_pos_odd_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralPositivityFinite.lean)
-/
@[path]
private lemma dihedral_pos_odd_finite_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {k : ℕ}
-- given
  (hst : s ≠ t)
  (hm : M s t ≠ 0)
  (hk : 2 * k + 1 < M s t) :
-- imply
  IsPositive (wordSigma M (t :: altWordEven s t k) (e s)) := by
-- proof
  apply CoxeterGroup.dihedral_pos_odd_finite M s t hst hm k hk

/--
[dihedral_pos_even](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralPositivityFinite.lean)
-/
@[path]
private lemma dihedral_pos_even_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {k : ℕ}
-- given
  (hst : s ≠ t)
  (hk : 2 * k < M s t ∨ M s t = 0) :
-- imply
  IsPositive (wordSigma M (altWordEven s t k) (e s)) := by
-- proof
  apply CoxeterGroup.dihedral_pos_even M s t hst k hk

/--
[dihedral_pos_odd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralPositivityFinite.lean)
-/
@[path]
private lemma dihedral_pos_odd_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {k : ℕ}
-- given
  (hst : s ≠ t)
  (hk : 2 * k + 1 < M s t ∨ M s t = 0) :
-- imply
  IsPositive (wordSigma M (t :: altWordEven s t k) (e s)) := by
-- proof
  apply CoxeterGroup.dihedral_pos_odd M s t hst k hk


-- created on 2026-10-23
