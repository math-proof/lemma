import Lemma.Tensor.EqCast_0'0.of.Eq
import Lemma.Tensor.Resize0.eq.Zero
open Tensor


@[main]
private lemma main
  [Zero α]
  {s₁ s₂ s₃ : List ℕ}
-- given
  (d : Fin s₂.length) (n : ℕ)
  (h1 : Tensor α s₁ = Tensor α s₂) (hs1 : s₁ = s₂)
  (h2 : Tensor α (s₂.set d n) = Tensor α s₃) (hs2 : s₂.set d n = s₃) :
-- imply
  cast h2 ((cast h1 (0 : Tensor α s₁)).resize d n) = 0 :=
-- proof
  (congrArg (fun t => cast h2 (t.resize d n)) (Tensor.EqCast_0'0.of.Eq hs1)).trans
    ((congrArg (cast h2) (Tensor.Resize0.eq.Zero d n)).trans (Tensor.EqCast_0'0.of.Eq hs2))


-- created on 2026-09-16
