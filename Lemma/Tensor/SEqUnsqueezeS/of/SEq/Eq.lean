import Lemma.Tensor.SEqUnsqueezeS.of.SEq
import Def.Data.Holor.Unsqueeze
open Tensor


@[path]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h : A ≃ B)
  (h_d : d = d') :
-- imply
  A.unsqueeze d ≃ B.unsqueeze d' := by
-- proof
  subst h_d
  apply SEqUnsqueezeS.of.SEq h


-- created on 2026-07-10
