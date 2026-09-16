import sympy.vector.Basic
import Lemma.Vector.EqGet0_0


@[main]
private lemma main
  [Zero γ] [Zero δ]
-- given
  {n : ℕ}
  {u : List.Vector β n}
  (f : β → γ → δ)
  (hf : ∀ b, f b 0 = 0) :
-- imply
  List.Vector.map₂ f u (0 : List.Vector γ n) = 0 := by
-- proof
  ext i
  rw [List.Vector.get_map₂]
  simp only [Vector.EqGet0_0.fin]
  exact hf _


-- created on 2026-09-15
