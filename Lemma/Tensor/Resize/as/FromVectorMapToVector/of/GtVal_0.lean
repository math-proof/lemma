import Lemma.Bool.SEqCast.of.Eq
import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
import Lemma.List.Set.eq.Cons_Set.of.GtLength_0
import sympy.tensor.tensor
open Bool List


@[main, cast]
private lemma main
  [Zero α]
  {s : List ℕ}
  {i : Fin s.length}
-- given
  (X : Tensor α s)
  (h_i : i.val > 0)
  (n : ℕ) :
-- imply
  X.resize i n ≃ Tensor.fromVector (X.toVector.map fun s => s.resize ⟨i - 1, by grind⟩ n) := by
-- proof
  match h_match : i with
  | ⟨0, h_i⟩ =>
    nomatch h_i
  | ⟨j + 1, h_i⟩ =>
    conv_lhs => unfold Tensor.resize
    simp
    apply SEqCast.of.Eq
    rw [HeadD.eq.Get_0.of.GtLength_0 (by grind)]
    rw [← Set.eq.Cons_Set.of.GtLength_0]


-- created on 2026-07-10
