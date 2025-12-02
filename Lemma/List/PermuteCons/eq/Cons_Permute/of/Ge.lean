import Lemma.List.Cons_Append.eq.AppendCons
import Lemma.List.Permute__Neg.eq.Append_AppendRotateDropTake
import Lemma.List.TakeCons.eq.Cons_Take
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.Nat.SubAdd.eq.AddSub.of.Ge
open List Nat


@[main]
private lemma main
  {s : List α}
  {i : Fin s.length}
  {d : ℕ}
-- given
  (h_d : i ≥ d) :
-- imply
  (s₀ :: s).permute ⟨i + 1, by simp⟩ (-d) = s₀ :: s.permute i (-d) := by
-- proof
  simp [Permute__Neg.eq.Append_AppendRotateDropTake.simp]
  rw [SubAdd.eq.AddSub.of.Ge h_d]
  rw [TakeCons.eq.Cons_Take]
  rw [AppendCons.eq.Cons_Append]
  simp
  repeat rw [EqMin.of.Le (by omega)]


-- created on 2025-10-31
