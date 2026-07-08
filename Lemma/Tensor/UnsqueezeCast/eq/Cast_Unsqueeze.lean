import Lemma.Tensor.UnsqueezeCast.as.Unsqueeze.of.Eq
import Lemma.List.EqSwap_0'1
import stdlib.SEq
import sympy.Basic
import sympy.tensor.Basic
open List Tensor Nat


@[main]
private lemma main
-- given
  (B : Tensor α [l, n]) :
-- imply
  have h_s : [l, n].swap ([l, n].length - 2) ([l, n].length - 1) = [n, l] := by
    simp [EqSwap_0'1]
  (cast (congrArg (Tensor α) h_s) Bᵀ).unsqueeze 0 = cast (congrArg (Tensor α) (by grind)) (Bᵀ.unsqueeze 0) := by
-- proof
  apply UnsqueezeCast.eq.Cast_Unsqueeze.of.Eq
  rfl


-- created on 2026-07-08
