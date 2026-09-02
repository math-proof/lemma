import Lemma.Tensor.DotHstack.eq.AddDotS
import Lemma.Tensor.DotAppend.eq.AppendDotS
open Tensor


/--
2×1 block matrix times a split vector.
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
  rw [DotAppend.eq.AppendDotS.mv (A.hstack B) (C.hstack D) (x ++ y)]
  have h0inv : (A.hstack B) @ (x ++ y) = cast (by simp [matmul_shape]) (cast (by simp [matmul_shape]) ((A.hstack B) @ (x ++ y)) : Tensor α [n]) := by
    simp
  have h1inv : (C.hstack D) @ (x ++ y) = cast (by simp [matmul_shape]) (cast (by simp [matmul_shape]) ((C.hstack D) @ (x ++ y)) : Tensor α [m]) := by
    simp
  rw [h0inv, h1inv, DotHstack.eq.AddDotS.mv A B x y, DotHstack.eq.AddDotS.mv C D x y]
  grind


-- created on 2020-08-18
-- updated on 2026-08-24
