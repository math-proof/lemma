import Mathlib
import Def.Analysis.Misc.erdos_707.Part2


namespace Mainstep

export Hypotheses (p hp N  hN B hdiff embed h_embed h_inj)

variable [Hypotheses]

lemma f_def {a:ZMod N} (ha: a ∉ B) (b:B) : a - b = f ha b - g ha b := by
  unfold f g
  exact (hdiff (a - b.val) (by grind)).choose_spec.1.symm

lemma f_def' {a:ZMod N} (ha: a ∉ B) (b c d:B) : a - b = c - d ↔ c = f ha b ∧ d = g ha b := by
  constructor
  . intro h
    rw [f_def ha b] at h; symm at h
    apply diff_uniq _ h
    rw [←f_def ha b] at h
    grind
  rintro ⟨ rfl, rfl ⟩
  exact f_def ha b

/-- {lean}`f (a := a)` is an involution. -/
lemma f_inv {a:ZMod N} (ha: a ∉ B) : Function.Involutive (f ha) := by
  intro b
  have h1 := f_def ha b
  replace h1 : a - (f ha b) = b - (g ha b) := by grind
  rw [f_def' ha] at h1
  rw [←h1.1]

/-- Fixed points of {lean}`f (a := a)` satisfy {lean}`2 * f ha b = a + g ha b`. -/
lemma f_fixed {a:ZMod N} {ha: a ∉ B} {b:B} (hb: f ha b = b): 2 * b.val = a + (g ha b).val := by
  have := f_def ha b
  grind

end Mainstep
