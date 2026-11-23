module

public import Mathlib.Tactic

@[expose] public section

/-!
# Interleaved Embeddings of `Fin d` into `Fin (d + d)`

`Fin.stepEven t = 2 * t` and `Fin.stepOdd t = 2 * t + 1`, the two coordinates of the
interleaved pair indexed by `t : Fin d` inside `Fin (d + d)`.
-/

namespace Fin

/-- Even coordinate `2t` of an interleaved pair in `Fin (d + d)`. -/
def stepEven {d : ℕ} (t : Fin d) : Fin (d + d) :=
  ⟨2 * (t : ℕ), by
    have ht := t.isLt
    omega⟩

/-- Odd coordinate `2t + 1` of an interleaved pair in `Fin (d + d)`. -/
def stepOdd {d : ℕ} (t : Fin d) : Fin (d + d) :=
  ⟨2 * (t : ℕ) + 1, by
    have ht := t.isLt
    omega⟩

end Fin
