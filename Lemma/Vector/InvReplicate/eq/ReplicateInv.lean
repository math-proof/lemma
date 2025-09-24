import stdlib.List.Vector.Basic
import Lemma.Basic


@[main]
private lemma main
  [Inv α]
-- given
  (a : α) :
-- imply
  (List.Vector.replicate n a)⁻¹ = List.Vector.replicate n a⁻¹ := by
-- proof
  simp [Inv.inv]
  ext i
  simp


-- created on 2025-09-24
