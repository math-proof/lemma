import Lemma.Tensor.DotHstack.eq.AddDotS
import Lemma.Tensor.DotAppend.eq.AppendDotS
import Instance.Data.Vector.Basic.Dot
open Tensor


/--
2×1 block matrix times a split vector.
-/
@[path]
private lemma main
  [Mul α] [AddCommMonoid α]
-- given
  (A : Tensor α [n, k])
  (B : Tensor α [n, l])
  (C : Tensor α [m, k])
  (D : Tensor α [m, l])
  (x : Tensor α [k])
  (y : Tensor α [l]) :
-- imply
  (A.hstack B ++ C.hstack D) ⬝ᵥ (x ++ y) = id (α := Tensor α [n]) (A ⬝ᵥ x) + id (α := Tensor α [n]) (B ⬝ᵥ y) ++ (id (α := Tensor α [m]) (C ⬝ᵥ x) + id (α := Tensor α [m]) (D ⬝ᵥ y)) := by
-- proof
  rw [DotAppend.eq.AppendDotS.mv (A.hstack B) (C.hstack D) (x ++ y)]
  have h0 := DotHstack.eq.AddDotS.mv A B x y
  have h1 := DotHstack.eq.AddDotS.mv C D x y
  simp only [id] at h0 h1 ⊢
  rw [h0, h1]


-- created on 2020-08-18
-- updated on 2026-11-13
