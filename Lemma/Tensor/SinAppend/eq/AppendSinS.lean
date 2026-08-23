import sympy.tensor.functions
import Lemma.Tensor.MapAppend.eq.AppendMapS
open Tensor


/--
Sine distributes over vertical block concatenation.
-/
@[main, comm]
private lemma main
  [Sin α]
-- given
  (A : Tensor α (n :: s))
  (B : Tensor α (m :: s)) :
-- imply
  (A ++ B).sin = A.sin ++ B.sin :=
-- proof
  MapAppend.eq.AppendMapS A B Sin.sin


-- created on 2023-06-08
-- updated on 2026-08-23
