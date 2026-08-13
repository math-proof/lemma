import Lemma.Tensor.CastDiv.eq.DivCast.of.Eq
import Lemma.Tensor.Dot.eq.SumMul.of.Lt
import Lemma.Tensor.MulDiv.eq.DivMul
import Lemma.Tensor.RepeatDiv.eq.DivRepeat
import Lemma.Tensor.ResizeDiv.eq.DivResize
import Lemma.Tensor.SumDiv.eq.DivSum
import Lemma.Tensor.UnsqueezeDiv.eq.DivUnsqueeze
open Tensor


@[main]
private lemma main
  [Semifield α]
-- given
  (h : k' < k)
  (A : Tensor α [m, k'])
  (C : Tensor α [k, n])
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  let A_div_r := (A / B).resize ⟨1, by grind⟩ k
  let A_r := A.resize ⟨1, by grind⟩ k
  have hr : A_div_r = A_r / B := by
    simp only [A_div_r, A_r]
    exact ResizeDiv.eq.DivResize A B ⟨1, by grind⟩ k
  let A_div0 : Tensor α [m, 1, k] := A_div_r.unsqueeze 1
  let A0 : Tensor α [m, 1, k] := A_r.unsqueeze 1
  have h0 : A_div0 = A0 / B := by
    simp only [A_div0, A0, hr]
    convert UnsqueezeDiv.eq.DivUnsqueeze A_r B 1 <;> simp
  let A_div : Tensor α [m, n, k] := cast (congrArg (Tensor α) (by simp)) (A_div0.repeat ⟨1, by grind⟩ n)
  let A' : Tensor α [m, n, k] := cast (congrArg (Tensor α) (by simp)) (A0.repeat ⟨1, by grind⟩ n)
  let CT : Tensor α [n, k] := Cᵀ
  let C0 : Tensor α [1, n, k] := CT.unsqueeze 0
  let C' : Tensor α [m, n, k] := cast (congrArg (Tensor α) (by simp)) (C0.repeat ⟨0, by grind⟩ m)
  have hA : A_div = A' / B := by
    simp only [A_div, A']
    rw [h0, RepeatDiv.eq.DivRepeat A0 B ⟨1, by grind⟩ n]
    apply CastDiv.eq.DivCast.of.Eq
    simp
  have hL : (A / B) @ C = (A_div * C').sum 2 := by
    simpa [A_div, A_div0, A_div_r, C', C0, CT] using Dot.eq.SumMul.of.Lt h (A / B) C
  have hR : A @ C = (A' * C').sum 2 := by
    simpa [A', A0, A_r, C', C0, CT] using Dot.eq.SumMul.of.Lt h A C
  rw [hL, hR, hA, MulDiv.eq.DivMul]
  apply SumDiv.eq.DivSum


-- created on 2026-08-13
