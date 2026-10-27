import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[list_skip_index](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ListAlternating.lean)
-/
@[path]
lemma list_skip_index
  {w : List α}
-- given
  (hw : w.length ≥ 2)
  (h_skip : ∀ k (hk : k + 2 < w.length), w[k]'(by omega) = w[k+2]'(by omega)) :
-- imply
  ∀ (i : ℕ) (hi : i < w.length), w[i]'hi = if i % 2 = 0 then w[0]'(by omega) else w[1]'(by omega) := by
-- proof
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro hi
    match i, ih with
    | 0, _ => simp
    | 1, _ => simp
    | i + 2, ih =>
      have hi2 : i < w.length := by omega
      have hskip := h_skip i (by omega)
      rw [← hskip, ih i (by omega) hi2]
      simp only [show (i + 2) % 2 = i % 2 from by omega]


-- created on 2026-10-23
