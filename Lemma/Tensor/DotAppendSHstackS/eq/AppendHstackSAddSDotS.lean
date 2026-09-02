import Lemma.Tensor.AddHstackS.eq.HstackAddS
import Lemma.Tensor.Dot_Hstack.eq.HstackDotS
import Lemma.Tensor.DotAppend.eq.AppendDotS
import Lemma.Tensor.DotHstack.eq.AddDotS
open Tensor


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.DotAppendSHstackS.eq.AppendHstackSAddSDotS |
| comm | Tensor.AppendHstackSAddSDotS.eq.DotAppendSHstackS |
-/
@[main, comm]
private lemma main
  [Mul α] [AddCommMonoid α]
-- given
  (A : Tensor α [n, k])
  (B : Tensor α [n, l])
  (C : Tensor α [m, k])
  (D : Tensor α [m, l])
  (X : Tensor α [k, p])
  (Y : Tensor α [k, q])
  (U : Tensor α [l, p])
  (V : Tensor α [l, q]) :
-- imply
  (A.hstack B ++ C.hstack D) @ (X.hstack Y ++ U.hstack V) = ((id (α := Tensor α [n, p]) (A @ X) + id (α := Tensor α [n, p]) (B @ U)).hstack (id (α := Tensor α [n, q]) (A @ Y) + id (α := Tensor α [n, q]) (B @ V))) ++ ((id (α := Tensor α [m, p]) (C @ X) + id (α := Tensor α [m, p]) (D @ U)).hstack (id (α := Tensor α [m, q]) (C @ Y) + id (α := Tensor α [m, q]) (D @ V))) := by
-- proof
  rw [DotAppend.eq.AppendDotS (A.hstack B) (C.hstack D) (X.hstack Y ++ U.hstack V)]
  have h0inv : (A.hstack B) @ (X.hstack Y ++ U.hstack V) = cast (by simp [matmul_shape, broadcast_shape]) (cast (by simp [matmul_shape, broadcast_shape]) ((A.hstack B) @ (X.hstack Y ++ U.hstack V)) : Tensor α [n, p + q]) := by
    simp
  have h1inv : (C.hstack D) @ (X.hstack Y ++ U.hstack V) = cast (by simp [matmul_shape, broadcast_shape]) (cast (by simp [matmul_shape, broadcast_shape]) ((C.hstack D) @ (X.hstack Y ++ U.hstack V)) : Tensor α [m, p + q]) := by
    simp
  rw [h0inv, h1inv, DotHstack.eq.AddDotS A B (X.hstack Y) (U.hstack V), DotHstack.eq.AddDotS C D (X.hstack Y) (U.hstack V)]
  rw [Dot_Hstack.eq.HstackDotS A X Y, Dot_Hstack.eq.HstackDotS B U V, Dot_Hstack.eq.HstackDotS C X Y, Dot_Hstack.eq.HstackDotS D U V]
  have hAdd0 := AddHstackS.eq.HstackAddS (id (α := Tensor α [n, p]) (A @ X)) (id (α := Tensor α [n, p]) (B @ U)) (id (α := Tensor α [n, q]) (A @ Y)) (id (α := Tensor α [n, q]) (B @ V))
  have hAdd1 := AddHstackS.eq.HstackAddS (id (α := Tensor α [m, p]) (C @ X)) (id (α := Tensor α [m, p]) (D @ U)) (id (α := Tensor α [m, q]) (C @ Y)) (id (α := Tensor α [m, q]) (D @ V))
  grind


-- created on 2020-08-18
-- updated on 2026-09-02
