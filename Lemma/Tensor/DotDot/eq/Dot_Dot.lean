import Lemma.Fin.MulSum.eq.Sum_Mul
import Lemma.Fin.Sum.of.All_Eq
import Lemma.Fin.Sum_BFn
import Lemma.Finset.Mul_Sum.eq.Sum_Mul
import Lemma.Tensor.GetDotDot.eq.DotDotGet
import Lemma.Tensor.GetDot_Dot.eq.Dot_Dot_GetT
import Lemma.Tensor.Get.of.Eq
import Lemma.Tensor.Sum_0.eq.Sum_Get
import Lemma.Vector.GetMul.eq.MulGet
open Tensor Fin Vector
set_option maxHeartbeats 1000000


private lemma mul_nil
  [Mul α]
-- given
  (a b : Tensor α []) :
-- imply
  Mul.mul a b = HMul.hMul (γ := Tensor α []) (self := instHMulTensorNilNatOfMul) a b := by
-- proof
  apply Eq.of.EqDataS
  change a.data * b.data = a.data * b.data[0]
  apply Vector.Eq.of.All_EqGetS.fin
  intro t
  rw [Vector.GetMul.eq.MulGetS.fin a.data b.data t, Vector.GetMul.eq.MulGet.fin a.data b.data[0] t]
  fin_cases t
  rfl


/--
tensor version of Matrix.mul_assoc
-/
@[main]
private lemma main
  [NonUnitalSemiring α]
-- given
  (L : Tensor α [l, m])
  (M : Tensor α [m, n])
  (N : Tensor α [n, o]) :
-- imply
  (L @ M) @ N = L @ (M @ N) := by
-- proof
  apply Tensor.Eq.of.All_EqGetS.fin
  intro i
  apply Tensor.Eq.of.All_EqGetS.fin
  intro j
  apply (GetDotDot.eq.DotDotGet L M N i j).trans
  apply Eq.trans _ (GetDot_Dot.eq.Dot_Dot_GetT L M N i j).symm
  let Li : Tensor α [m] := L[i]
  let Nj : Tensor α [n] := Nᵀ[j]
  apply (Dot.eq.SumMul__0 (Li @ M) Nj).trans
  apply Eq.trans _ (Dot.eq.SumMul__0 Li (M @ Nj)).symm
  let LM : Tensor α [n] := Li @ M
  let MN : Tensor α [m] := M @ Nj
  apply (Sum_0.eq.Sum_Get (LM * Nj)).trans
  apply Eq.trans _ (Sum_0.eq.Sum_Get (Li * MN)).symm
  trans ∑ k : Fin n, id (α := Tensor α []) LM[k] * id (α := Tensor α []) Nj[k]
  ·
    apply Sum.of.All_Eq
    intro k
    apply (GetMul.eq.MulGetS LM Nj k).trans
    apply mul_nil (a := (LM[k] : Tensor α [])) (b := (Nj[k] : Tensor α []))
  trans ∑ p : Fin m, id (α := Tensor α []) Li[p] * id (α := Tensor α []) MN[p]
  ·
    trans ∑ k : Fin n, (∑ p : Fin m, id (α := Tensor α []) Li[p] * id (α := Tensor α []) M[p][k]) * id (α := Tensor α []) Nj[k]
    ·
      apply Sum.of.All_Eq
      intro k
      rw [show LM[k] = (Li @ M)[k] by
        simp [LM, GetElem.getElem]
        rfl]
      apply congrArg (fun t => id (α := Tensor α []) t * id (α := Tensor α []) Nj[k])
      apply (Tensor.Get.of.Eq.fin (Dot.eq.GetDotUnsqueeze_0 Li M) k).trans
      apply (GetDot.eq.DotGetS (Li.unsqueeze 0) M ⟨0, by simp⟩ k).trans
      apply Eq.trans
      ·
        apply congrArg (fun t : Tensor α [m] => t @ (Mᵀ[k] : Tensor α [m]))
        apply EqGetUnsqueeze_0.nat
      let Mj : Tensor α [m] := Mᵀ[k]
      apply (Dot.eq.SumMul__0 Li Mj).trans
      apply (Sum_0.eq.Sum_Get (Li * Mj)).trans
      apply Sum.of.All_Eq
      intro p
      apply (GetMul.eq.MulGetS Li Mj p).trans
      rw [show Mj[p] = M[p][k] by
        simp only [Mj]
        apply (Tensor.Get.of.Eq.fin (GetT.eq.Select M k) p).trans
        apply Bool.Eq.of.SEq
        apply
          (GetSelect_1.as.Get.of.Lt.GtGet_0.GtLength_0
            (s := [n]) (n := m) (i := ↑k) (j := ↑p)
            (by simp) (by simp) p.isLt M).trans
        simp
        rfl]
      apply mul_nil (a := (Li[p] : Tensor α [])) (b := (M[p][k] : Tensor α []))
    trans ∑ k : Fin n, ∑ p : Fin m, (id (α := Tensor α []) Li[p] * id (α := Tensor α []) M[p][k]) * id (α := Tensor α []) Nj[k]
    ·
      apply Sum.of.All_Eq
      intro k
      let f := fun p : Fin m => id (α := Tensor α []) Li[p] * id (α := Tensor α []) M[p][k]
      let x := id (α := Tensor α []) Nj[k]
      change (∑ p : Fin m, f p) * x = ∑ p : Fin m, f p * x
      apply Eq.trans (mul_nil (∑ p : Fin m, f p) x).symm
      apply Eq.trans (MulSum.eq.Sum_Mul f)
      apply Sum.of.All_Eq
      intro p
      apply mul_nil
    trans ∑ p : Fin m, ∑ k : Fin n, (id (α := Tensor α []) Li[p] * id (α := Tensor α []) M[p][k]) * id (α := Tensor α []) Nj[k]
    ·
      apply Sum_BFn.comm
    trans ∑ p : Fin m, ∑ k : Fin n, id (α := Tensor α []) Li[p] * (id (α := Tensor α []) M[p][k] * id (α := Tensor α []) Nj[k])
    ·
      apply Sum.of.All_Eq
      intro p
      apply Sum.of.All_Eq
      intro k
      let a := id (α := Tensor α []) Li[p]
      let b := id (α := Tensor α []) M[p][k]
      let c := id (α := Tensor α []) Nj[k]
      change (a * b) * c = a * (b * c)
      rw [(mul_nil a b).symm]
      rw [(mul_nil (Mul.mul a b) c).symm]
      apply Eq.trans (Nat.MulMul.eq.Mul_Mul (a := a) (b := b) (c := c))
      rw [(mul_nil b c).symm]
      apply mul_nil a (Mul.mul b c)
    trans ∑ p : Fin m, id (α := Tensor α []) Li[p] * ∑ k : Fin n, id (α := Tensor α []) M[p][k] * id (α := Tensor α []) Nj[k]
    ·
      apply Sum.of.All_Eq
      intro p
      apply Eq.symm
      let a := id (α := Tensor α []) Li[p]
      let f := fun k : Fin n => id (α := Tensor α []) M[p][k] * id (α := Tensor α []) Nj[k]
      change a * ∑ k : Fin n, f k = ∑ k : Fin n, a * f k
      apply Eq.trans (mul_nil a (∑ k : Fin n, f k)).symm
      apply Eq.trans (Finset.Mul_Sum.eq.Sum_Mul (s := Finset.univ) f a)
      apply Sum.of.All_Eq
      intro k
      apply mul_nil
    apply Sum.of.All_Eq
    intro p
    rw [show MN[p] = (M @ Nj)[p] by
      simp [MN, GetElem.getElem]
      rfl]
    apply congrArg (fun t => id (α := Tensor α []) Li[p] * id (α := Tensor α []) t)
    symm
    apply (GetDot.eq.DotGet.une M Nj p).trans
    let Mi : Tensor α [n] := M[p]
    apply (Dot.eq.SumMul__0 Mi Nj).trans
    apply (Sum_0.eq.Sum_Get (Mi * Nj)).trans
    apply Sum.of.All_Eq
    intro k
    apply (GetMul.eq.MulGetS Mi Nj k).trans
    simp [id, Mi]
    apply mul_nil
  ·
    apply Sum.of.All_Eq
    intro p
    apply Eq.symm
    apply (GetMul.eq.MulGetS Li MN p).trans
    apply mul_nil (a := (Li[p] : Tensor α [])) (b := (MN[p] : Tensor α []))


-- created on 2025-05-03
-- updated on 2026-08-27
