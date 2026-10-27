import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.Roots
open Finset BigOperators CoxeterGroup


namespace CoxeterGroup

/--
[neg_isPositive_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/Roots.lean)
-/
@[path]
private lemma neg_isPositive_iff
  [DecidableEq B]
  [Fintype B]
  {v : B → ℝ} :
-- imply
  IsPositive (-v) ↔ IsNegative v := by
-- proof
  simp only [IsPositive, IsNegative, Pi.neg_apply, neg_nonneg]

end CoxeterGroup

namespace CoxeterGroup

/--
[IsPositive.smul_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/Roots.lean)
-/
@[path]
private lemma IsPositive.smul_nonneg
  [DecidableEq B]
  [Fintype B]
  {v : B → ℝ}
  {c : ℝ}
-- given
  (hv : IsPositive v)
  (hc : 0 ≤ c) :
-- imply
  IsPositive (c • v) := by
-- proof
  intro s
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_nonneg hc (hv s)

end CoxeterGroup

namespace CoxeterGroup

/--
[IsPositive.add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/Roots.lean)
-/
@[path]
private lemma IsPositive.add
  [DecidableEq B]
  [Fintype B]
  {v w : B → ℝ}
-- given
  (hv : IsPositive v)
  (hw : IsPositive w) :
-- imply
  IsPositive (v + w) := by
-- proof
  intro s
  simp only [Pi.add_apply]
  linarith [hv s, hw s]

end CoxeterGroup

/--
[formVal_nonpos_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/Roots.lean)
-/
@[path]
private lemma formVal_nonpos_of_ne_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
-- given
  (hst : s ≠ t) :
-- imply
  formVal M s t ≤ 0 := by
-- proof
  apply CoxeterGroup.formVal_nonpos_of_ne M s t hst

/--
[sigmaLin_preserves_positive_off_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/Roots.lean)
-/
@[path]
private lemma sigmaLin_preserves_positive_off_diagonal_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
-- given
  (hst : s ≠ t) :
-- imply
  IsPositive (sigmaLin M s (e t)) := by
-- proof
  apply CoxeterGroup.sigmaLin_preserves_positive_off_diagonal M s t hst

/--
[sigma_coord_ne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/Roots.lean)
-/
@[path]
private lemma sigma_coord_ne_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s : B}
  {v : B → ℝ}
  {t : B}
-- given
  (hts : t ≠ s) :
-- imply
  sigma M s v t = v t := by
-- proof
  apply CoxeterGroup.sigma_coord_ne M s v t hts

/--
[sigma_coord_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/Roots.lean)
-/
@[path]
private lemma sigma_coord_self_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s : B}
  {v : B → ℝ} :
-- imply
  sigma M s v s = v s - 2 * bilinForm M v (e s) := by
-- proof
  apply CoxeterGroup.sigma_coord_self M s v


-- created on 2026-10-23
-- updated on 2026-10-26
