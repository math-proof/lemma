import Lemma.List.EqPermute__0
import Lemma.Nat.LeAdd_1
import Lemma.Tensor.SumCast.as.Sum.of.Eq
import Lemma.Tensor.SumPermute.as.PermuteSum.of.Ge.EqAdd_1Length
import Lemma.Tensor.SumPermute.as.PermuteSum.of.Ge.LtAdd_1Length
open List Nat Tensor


@[main]
private lemma main
  [AddCommMonoid α]
  {i : Fin s.length}
  {d : ℕ}
-- given
  (h : i ≥ d)
  (X : Tensor α s) :
-- imply
  (X.permute i (-d)).sum (i - d) ≃ X.sum i := by
-- proof
  if h_d : d = 0 then
    subst h_d
    simp
    apply SumCast.as.Sum.of.Eq
    rw [EqPermute__0]
  else
    have : NeZero d := ⟨h_d⟩
    if h_i : i.val + 1 = s.length then
      apply SumPermute.as.PermuteSum.of.Ge.EqAdd_1Length h_i h
    else
      apply SumPermute.as.PermuteSum.of.Ge.LtAdd_1Length _ h
      apply Lt.of.Le.Ne _ h_i
      apply LeAdd_1


-- created on 2025-10-31
-- updated on 2025-11-16
