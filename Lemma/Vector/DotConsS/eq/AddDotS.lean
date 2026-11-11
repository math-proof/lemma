import Instance.Data.Vector.Basic.Dot
import Lemma.Vector.Dot.eq.Add_Dot
open Vector


@[path]
private lemma main
  [Add α] [Zero α] [Mul α]
-- given
  (a a' : α)
  (s s' : List.Vector α n) :
-- imply
  (a ::ᵥ s) ⬝ᵥ (a' ::ᵥ s') = a * a' + s ⬝ᵥ s' := by
-- proof
  rw [Dot.eq.Add_Dot]
  rfl


-- created on 2024-07-01
-- updated on 2026-07-15
