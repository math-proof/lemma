import sympy.tensor.functions
import Lemma.Tensor.MapAppend.eq.AppendMapS
open Tensor


/--
Cosine distributes over vertical block concatenation.
-/
@[main, comm]
private lemma main
  [Cos α]
-- given
  (A : Tensor α (n :: s))
  (B : Tensor α (m :: s)) :
-- imply
  (A ++ B).cos = A.cos ++ B.cos :=
-- proof
  MapAppend.eq.AppendMapS A B Cos.cos


-- created on 2023-06-08
-- updated on 2026-08-23
