import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.SpiveyPQBell
open scoped BigOperators
open MetaMathlibExt


namespace MetaMathlibExt

/--
[spivey_bracket_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SpiveyPQBell.lean)
-/
@[path]
private lemma spivey_bracket_add (p q : ℝ) (hpq : p ≠ q) (k j : ℕ) :
  (p ^ (k + j) - q ^ (k + j)) / (p - q) =
    p ^ j * ((p ^ k - q ^ k) / (p - q)) +
      q ^ k * ((p ^ j - q ^ j) / (p - q)) := by
  rw [pow_add, pow_add]
  field_simp
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[spivey_bracket_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SpiveyPQBell.lean)
-/
@[path]
private lemma spivey_bracket_pos (p q : ℝ) (hq0 : 0 < q) (hqp : q < p)
  (k : ℕ) (hk : 0 < k) : 0 < (p ^ k - q ^ k) / (p - q) := by
  have hpows : q ^ k < p ^ k :=
    pow_lt_pow_left₀ hqp hq0.le (Nat.ne_of_gt hk)
  exact div_pos (sub_pos.mpr hpows) (sub_pos.mpr hqp)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[spivey_pq_bell](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SpiveyPQBell.lean)
-/
@[path]
lemma spivey_pq_bell
  :
-- imply
  ∀ (p q : ℝ) (hq0 : 0 < q) (hqp : q < p) (hp1 : p ≤ 1),
    let bracket : ℕ → ℝ := by
-- proof
  intro p q hq0 hqp hp1 bracket tildeS tildeB m n
  have hpq : p ≠ q := ne_of_gt hqp
  have hbracket0 : bracket 0 = 0 := by simp [bracket]
  have hbracketAdd : ∀ k j, bracket (k + j) = p ^ j * bracket k + q ^ k * bracket j := by
    exact spivey_bracket_add p q hpq
  have hbracket_ne : ∀ k, 0 < k → bracket k ≠ 0 := by
    intro k hk
    exact ne_of_gt (spivey_bracket_pos p q hq0 hqp k hk)
  dsimp only [tildeB, tildeS]
  run_tac spivey_finish_public

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
