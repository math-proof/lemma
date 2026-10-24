import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.RSW.Renorm
open Real StatMech StatMech.RSW StatMech.RSW.Renorm


/--
[rrn_renorm_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Renorm.lean)
-/
@[path]
private lemma rrn_renorm_iterate_eq
  {b : ℕ → ℝ}
-- given
  (hnn : ∀ k, 0 ≤ b k)
  (hsq : ∀ k, b (k + 1) ≤ (b k) ^ 2) :
-- imply
  ∀ k, b k ≤ (b 0) ^ (2 ^ k) := by
-- proof
  apply StatMech.RSW.Renorm.rrn_renorm_iterate b hnn hsq

/--
[rrn_super_exp_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Renorm.lean)
-/
@[path]
private lemma rrn_super_exp_decay_eq
  {b : ℕ → ℝ}
  {b₀ : ℝ}
-- given
  (hb0pos : 0 < b₀)
  (hb0 : b₀ < 1)
  (hgeom : ∀ k, b k ≤ b₀ ^ (2 ^ k)) :
-- imply
  ∃ c : ℝ, 0 < c ∧ ∀ k, b k ≤ Real.exp (-c * (2 ^ k : ℕ)) := by
-- proof
  apply StatMech.RSW.Renorm.rrn_super_exp_decay b hb0pos hb0 hgeom

/--
[rrn_renorm_super_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Renorm.lean)
-/
@[path]
private lemma rrn_renorm_super_exp_eq
  {b : ℕ → ℝ}
-- given
  (hnn : ∀ k, 0 ≤ b k)
  (hb0pos : 0 < b 0)
  (hb0 : b 0 < 1)
  (hsq : ∀ k, b (k + 1) ≤ (b k) ^ 2) :
-- imply
  ∃ c : ℝ, 0 < c ∧ ∀ k, b k ≤ Real.exp (-c * (2 ^ k : ℕ)) := by
-- proof
  apply StatMech.RSW.Renorm.rrn_renorm_super_exp b hnn hb0pos hb0 hsq

/--
[rrn_subunit_seed_of_not_bddBelow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Renorm.lean)
-/
@[path]
private lemma rrn_subunit_seed_of_not_bddBelow_eq
  {u : ℕ → ℝ}
  {C : ℝ}
  {n₀ : ℕ}
-- given
  (hC : 0 < C)
  (hnn : ∀ n, 0 ≤ u n)
  (hsmall : u n₀ < 1 / C) :
-- imply
  0 ≤ C * u n₀ ∧ C * u n₀ < 1 := by
-- proof
  apply StatMech.RSW.Renorm.rrn_subunit_seed_of_not_bddBelow hC hnn hsmall


-- created on 2026-10-23
