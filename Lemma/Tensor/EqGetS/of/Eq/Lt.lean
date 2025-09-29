import Lemma.Tensor.Eq.is.All_EqGetS
open Tensor


@[main]
private lemma main
  {m : ℕ}
  {X Y : Tensor α (m :: s)}
-- given
  (h₀ : n < m)
  (h₁ : X = Y) :
-- imply
  X[n] = Y[n] := by
-- proof
  have h_gets := All_EqGetS.of.Eq h₁
  specialize h_gets ⟨n, h₀⟩
  simp [GetElem.getElem] at h_gets ⊢
  assumption


-- created on 2025-09-29
