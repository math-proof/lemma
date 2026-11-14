import Lemma.Tensor.AddHstackS.eq.HstackAddS
import Lemma.Tensor.Dot_Hstack.eq.HstackDotS
import Lemma.Tensor.DotAppend.eq.AppendDotS
import Lemma.Tensor.DotHstack.eq.AddDotS
import Instance.Data.Vector.Basic.Dot
open Tensor


/--
| attributes | lemma |
| :---: | :---: |
| path | Tensor.DotAppendSHstackS.eq.AppendHstackSAddSDotS |
| comm | Tensor.AppendHstackSAddSDotS.eq.DotAppendSHstackS |
-/
@[path, comm]
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
  (A.hstack B ++ C.hstack D) ⬝ᵥ (X.hstack Y ++ U.hstack V) = ((id (α := Tensor α [n, p]) (A ⬝ᵥ X) + id (α := Tensor α [n, p]) (B ⬝ᵥ U)).hstack (id (α := Tensor α [n, q]) (A ⬝ᵥ Y) + id (α := Tensor α [n, q]) (B ⬝ᵥ V))) ++ ((id (α := Tensor α [m, p]) (C ⬝ᵥ X) + id (α := Tensor α [m, p]) (D ⬝ᵥ U)).hstack (id (α := Tensor α [m, q]) (C ⬝ᵥ Y) + id (α := Tensor α [m, q]) (D ⬝ᵥ V))) := by
-- proof
  rw [DotAppend.eq.AppendDotS (A.hstack B) (C.hstack D) (X.hstack Y ++ U.hstack V)]
  simp only [id]
  rw [DotHstack.eq.AddDotS A B (X.hstack Y) (U.hstack V), DotHstack.eq.AddDotS C D (X.hstack Y) (U.hstack V)]
  rw [Dot_Hstack.eq.HstackDotS A X Y, Dot_Hstack.eq.HstackDotS B U V, Dot_Hstack.eq.HstackDotS C X Y, Dot_Hstack.eq.HstackDotS D U V]
  have hAdd0 := AddHstackS.eq.HstackAddS (id (α := Tensor α [n, p]) (A ⬝ᵥ X)) (id (α := Tensor α [n, p]) (B ⬝ᵥ U)) (id (α := Tensor α [n, q]) (A ⬝ᵥ Y)) (id (α := Tensor α [n, q]) (B ⬝ᵥ V))
  have hAdd1 := AddHstackS.eq.HstackAddS (id (α := Tensor α [m, p]) (C ⬝ᵥ X)) (id (α := Tensor α [m, p]) (D ⬝ᵥ U)) (id (α := Tensor α [m, q]) (C ⬝ᵥ Y)) (id (α := Tensor α [m, q]) (D ⬝ᵥ V))
  grind


-- created on 2020-08-18
-- updated on 2026-11-13
