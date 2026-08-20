import Lemma.Tensor.GetSliceStack.as.Stack_UFnAdd.of.Eq
open Tensor


@[main]
private lemma main
  {n m start stop : ℕ}
-- given
  (h : (⟨start, stop, 1⟩ : Slice).length n = (⟨start, stop, 1⟩ : Slice).length m)
  (f : ℕ → Tensor α s) :
-- imply
  ([i < n] f i)[start:stop] ≃ ([i < m] f i)[start:stop] :=
-- proof
  (GetSliceStack.as.Stack_UFnAdd.of.Eq rfl f).trans (GetSliceStack.as.Stack_UFnAdd.of.Eq h.symm f).symm


-- created on 2026-08-20
