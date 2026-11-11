import Lemma.Fin.MulSum.eq.Sum_Mul
import Def.Data.Tensor.Sum
import Def.Data.Tensor.Unsqueeze
import Notation.Data.Tensor.Permute
import Lemma.Fin.Sum_BFn
import Lemma.Finset.Mul_Sum.eq.Sum_Mul
import Lemma.Tensor.Dot.eq.Sum_MulGetS
import Lemma.Tensor.GetDotDot.eq.DotDotGet
import Lemma.Tensor.GetDot_Dot.eq.Dot_Dot_GetT
import Lemma.Tensor.EqGetT
import Instance.Data.Vector.Basic.Dot
open Tensor Fin
set_option maxHeartbeats 500000


@[path]
private lemma vmv
  [NonUnitalSemiring α]
-- given
  (v : Tensor α [m])
  (M : Tensor α [m, n])
  (w : Tensor α [n]) :
-- imply
  (v ⬝ᵥ M) ⬝ᵥ w = v ⬝ᵥ (M ⬝ᵥ w) := by
-- proof
  apply (Dot.eq.Sum_MulGetS (v ⬝ᵥ M) w).trans
  apply Eq.trans _ (Dot.eq.Sum_MulGetS v (M ⬝ᵥ w)).symm
  trans ∑ k : Fin n, id (α := Tensor α []) (v ⬝ᵥ (Mᵀ[k] : Tensor α [m])) * id (α := Tensor α []) w[k]
  ·
    apply Sum.of.All_Eq
    intro k
    apply congrArg (fun t => id (α := Tensor α []) t * id (α := Tensor α []) w[k])
    apply (Tensor.Get.of.Eq.fin (Dot.eq.GetDotUnsqueeze_0 v M) k).trans
    apply (GetDot.eq.DotGetS (v.unsqueeze 0) M ⟨0, by simp⟩ k).trans
    apply congrArg (fun t : Tensor α [m] => t ⬝ᵥ (Mᵀ[k] : Tensor α [m]))
    apply EqGetUnsqueeze_0.nat
  trans ∑ k : Fin n, (∑ i : Fin m, id (α := Tensor α []) v[i] * id (α := Tensor α []) M[i][k]) * id (α := Tensor α []) w[k]
  ·
    apply Sum.of.All_Eq
    intro k
    apply congrArg (fun t => t * id (α := Tensor α []) w[k])
    apply Eq.trans (Dot.eq.Sum_MulGetS v (Mᵀ[k] : Tensor α [m]))
    apply Sum.of.All_Eq
    intro i
    apply congrArg (fun t => id (α := Tensor α []) v[i] * id (α := Tensor α []) t)
    apply EqGetT
  trans ∑ k : Fin n, ∑ i : Fin m, (id (α := Tensor α []) v[i] * id (α := Tensor α []) M[i][k]) * id (α := Tensor α []) w[k]
  ·
    apply Sum.of.All_Eq
    intro k
    let f := fun i : Fin m => id (α := Tensor α []) v[i] * id (α := Tensor α []) M[i][k]
    let x := id (α := Tensor α []) w[k]
    change (∑ i : Fin m, f i) * x = ∑ i : Fin m, f i * x
    apply Eq.trans (Mul _ _)
    apply Eq.trans (MulSum.eq.Sum_Mul f)
    apply Sum.of.All_Eq
    intro i
    apply (Mul _ _).symm
  trans ∑ i : Fin m, ∑ k : Fin n, (id (α := Tensor α []) v[i] * id (α := Tensor α []) M[i][k]) * id (α := Tensor α []) w[k]
  ·
    apply Sum_BFn.comm
  trans ∑ i : Fin m, ∑ k : Fin n, id (α := Tensor α []) v[i] * (id (α := Tensor α []) M[i][k] * id (α := Tensor α []) w[k])
  ·
    apply Sum.of.All_Eq
    intro i
    apply Sum.of.All_Eq
    intro k
    let a := id (α := Tensor α []) v[i]
    let b := id (α := Tensor α []) M[i][k]
    let c := id (α := Tensor α []) w[k]
    change (a * b) * c = a * (b * c)
    repeat rw [@Tensor.Mul]
    apply Eq.trans Nat.MulMul.eq.Mul_Mul
    rfl
  trans ∑ i : Fin m, id (α := Tensor α []) v[i] * ∑ k : Fin n, id (α := Tensor α []) M[i][k] * id (α := Tensor α []) w[k]
  ·
    apply Sum.of.All_Eq
    intro i
    apply Eq.symm
    let a := id (α := Tensor α []) v[i]
    let f := fun k : Fin n => id (α := Tensor α []) M[i][k] * id (α := Tensor α []) w[k]
    change a * ∑ k : Fin n, f k = ∑ k : Fin n, a * f k
    apply Eq.trans (Mul _ _)
    apply Eq.trans (Finset.Mul_Sum.eq.Sum_Mul (s := Finset.univ) f a)
    apply Sum.of.All_Eq
    intro k
    apply (Mul _ _).symm
  apply Sum.of.All_Eq
  intro i
  apply congrArg (fun t => id (α := Tensor α []) v[i] * id (α := Tensor α []) t)
  apply Eq.trans _ (GetDot.eq.DotGet.une M w i).symm
  apply Eq.symm
  apply Dot.eq.Sum_MulGetS


@[path]
private lemma vmm
  [NonUnitalSemiring α]
-- given
  (v : Tensor α [m])
  (M : Tensor α [m, n])
  (N : Tensor α [n, o]) :
-- imply
  (v ⬝ᵥ M) ⬝ᵥ N = v ⬝ᵥ (M ⬝ᵥ N) := by
-- proof
  apply Tensor.Eq.of.All_EqGetS.fin
  intro j
  apply (Tensor.Get.of.Eq.fin (Dot.eq.GetDotUnsqueeze_0 (v ⬝ᵥ M) N) j).trans
  apply (GetDot.eq.DotGetS ((v ⬝ᵥ M).unsqueeze 0) N ⟨0, by simp⟩ j).trans
  apply Eq.trans
  ·
    apply congrArg (fun t : Tensor α [n] => t ⬝ᵥ (Nᵀ[j] : Tensor α [n]))
    apply EqGetUnsqueeze_0.nat
  apply Eq.trans (vmv v M (Nᵀ[j] : Tensor α [n]))
  apply Eq.trans _ (Tensor.Get.of.Eq.fin (Dot.eq.GetDotUnsqueeze_0 v (M ⬝ᵥ N)) j).symm
  apply Eq.trans _ (GetDot_Dot.eq.Dot_Dot_GetT (v.unsqueeze 0) M N ⟨0, by simp⟩ j).symm
  apply congrArg (fun t : Tensor α [m] => t ⬝ᵥ (M ⬝ᵥ Nᵀ[j]))
  apply Eq.symm
  apply EqGetUnsqueeze_0


@[path]
private lemma mmv
  [NonUnitalSemiring α]
-- given
  (M : Tensor α [l, m])
  (N : Tensor α [m, n])
  (v : Tensor α [n]) :
-- imply
  (M ⬝ᵥ N) ⬝ᵥ v = M ⬝ᵥ (N ⬝ᵥ v) := by
-- proof
  apply Tensor.Eq.of.All_EqGetS.fin
  intro i
  apply (GetDot.eq.DotGet.une (M ⬝ᵥ N) v i).trans
  apply Eq.trans _ (GetDot.eq.DotGet.une M (N ⬝ᵥ v) i).symm
  apply Eq.trans (congrArg (fun t : Tensor α [n] => t ⬝ᵥ v) (GetDot.eq.DotGet M N i))
  apply vmv


/--
tensor version of Matrix.mul_assoc
-/
@[path]
private lemma main
  [NonUnitalSemiring α]
-- given
  (L : Tensor α [l, m])
  (M : Tensor α [m, n])
  (N : Tensor α [n, o]) :
-- imply
  (L ⬝ᵥ M) ⬝ᵥ N = L ⬝ᵥ (M ⬝ᵥ N) := by
-- proof
  apply Tensor.Eq.of.All_EqGetS.fin
  intro i
  apply Tensor.Eq.of.All_EqGetS.fin
  intro j
  apply (GetDotDot.eq.DotDotGet L M N i j).trans
  apply Eq.trans _ (GetDot_Dot.eq.Dot_Dot_GetT L M N i j).symm
  apply vmv


-- created on 2025-05-03
-- updated on 2026-10-26
