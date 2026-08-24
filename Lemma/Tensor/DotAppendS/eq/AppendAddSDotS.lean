import Lemma.Tensor.DotHstack.eq.AddDotS
import Lemma.Tensor.DotAppend.eq.AppendDotS
open Tensor


/--
2×2 block matrix times a split vector.
-/
@[main]
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
  (A.hstack B ++ C.hstack D) @ (x ++ y) = (id (α := Tensor α [n]) (A @ x) + id (α := Tensor α [n]) (B @ y)) ++ (id (α := Tensor α [m]) (C @ x) + id (α := Tensor α [m]) (D @ y)) := by
-- proof
  have hsplit := DotAppend.eq.AppendDotS.mv (Tensor.hstack A B) (Tensor.hstack C D) (x ++ y)
  rw [hsplit]
  have h0 := DotHstack.eq.AddDotS A B x y
  have h1 := DotHstack.eq.AddDotS C D x y
  have h0inv : (Tensor.hstack A B) @ (x ++ y) = cast (by simp [matmul_shape]) (cast (by simp [matmul_shape]) ((Tensor.hstack A B) @ (x ++ y)) : Tensor α [n]) := by
    simp
  have h1inv : (Tensor.hstack C D) @ (x ++ y) = cast (by simp [matmul_shape]) (cast (by simp [matmul_shape]) ((Tensor.hstack C D) @ (x ++ y)) : Tensor α [m]) := by
    simp
  rw [h0inv, h1inv, h0, h1]
  simp


-- created on 2020-08-18
-- updated on 2026-08-24
