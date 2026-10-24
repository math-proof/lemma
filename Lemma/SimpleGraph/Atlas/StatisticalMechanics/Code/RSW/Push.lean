import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.RSW.Push
open StatMech StatMech.RSW StatMech.RSW.Push


/--
[rpu_push_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Push.lean)
-/
@[path]
private lemma rpu_push_lower_eq
  {g : ℕ → ℝ}
  {β : ℝ}
-- given
  (hβ : 0 < β)
  (hbase : β ≤ g 0)
  (hstep : ∀ j, g j * β ≤ g (j + 1)) :
-- imply
  ∀ j, β ^ (j + 1) ≤ g j := by
-- proof
  apply StatMech.RSW.Push.rpu_push_lower g hβ hbase hstep

/--
[rpu_push_constant_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Push.lean)
-/
@[path]
private lemma rpu_push_constant_pos_eq
  {g : ℕ → ℝ}
  {β : ℝ}
-- given
  (hβ : 0 < β)
  (hbase : β ≤ g 0)
  (hstep : ∀ j, g j * β ≤ g (j + 1)) :
-- imply
  ∀ j, 0 < g j := by
-- proof
  apply StatMech.RSW.Push.rpu_push_constant_pos g hβ hbase hstep

/--
[rpu_push_constant_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Push.lean)
-/
@[path]
private lemma rpu_push_constant_eq_eq
  {β : ℝ}
  {j : ℕ} :
-- imply
  (fun i => β ^ (i + 1)) (j + 1) = (fun i => β ^ (i + 1)) j * β := by
-- proof
  apply StatMech.RSW.Push.rpu_push_constant_eq j

/--
[rpu_push](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Push.lean)
-/
@[path]
private lemma rpu_push_eq
  {g : ℕ → ℕ → ℝ}
  {β : ℝ}
-- given
  (hβ : 0 < β)
  (hbase : ∀ n, β ≤ g 0 n)
  (hstep : ∀ j n, g j n * β ≤ g (j + 1) n) :
-- imply
  ∀ j, ∃ c : ℝ, 0 < c ∧ ∀ n, c ≤ g j n := by
-- proof
  apply StatMech.RSW.Push.rpu_push g hβ hbase hstep


-- created on 2026-10-23
