import Lemma.Tensor.Select.eq.FromVectorMapToVector.of.GtLength
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
open Tensor


@[main, cast]
private lemma main
  {s : List ℕ}
  {d : Fin s.length}
-- given
  (h_d : d.val > 0)
  (X : Tensor α s)
  (i : Fin s[d]) :
-- imply
  X.select d i ≃ Tensor.fromVector (X.toVector.map (·.select ⟨d - 1, by grind⟩ ⟨i, by grind⟩)) := by
-- proof
  match s with
  | [] =>
    nomatch d
  | n :: s =>
    match d with
    | ⟨0, _⟩ =>
      nomatch h_d
    | ⟨j + 1, h⟩ =>
      have h_j : s.length > j := Nat.lt_succ_iff.mp h
      have hi : i < s[j] := i.isLt
      apply SEq.of.SEqDataS.Eq
      ·
        simp
      ·
        rw [Select.eq.FromVectorMapToVector.of.GtLength (X := X) (d := j) (i := ⟨i, hi⟩) (h := h_j)]
        rfl


-- created on 2026-07-23
