import Lemma.Tensor.DataMul.eq.MulData
import Lemma.Tensor.DataMul.eq.Mul_Data
import Lemma.Tensor.DetMul.eq.MulProd
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetMul.eq.MulGet
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.MulStack.eq.Stack_Mul
import Lemma.Tensor.Prod_0.eq.Prod_Get
import Lemma.Tensor.Pow.eq.TensorListPow
import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Vector.GetMul.eq.MulGet
import Lemma.Vector.GetMul.eq.Mul_Get
import sympy.tensor.stack
import sympy.tensor.tensor
open Tensor


@[main]
private lemma main
  [CommRing α]
-- given
  (a : α)
  (X : Tensor α [n, n]) :
-- imply
  (a * X).det = a ^ n * X.det := by
-- proof
  let a0 : Tensor α [] := a
  let f : Fin n → Tensor α [] := fun _ => a0
  let v : Tensor α [n] := [i < n] f i
  have hAX : a * X = X * a := by
    apply Eq.of.EqDataS
    rw [DataMul.eq.Mul_Data, DataMul.eq.MulData]
    apply Vector.Eq.of.All_EqGetS.fin
    intro t
    rw [Vector.GetMul.eq.Mul_Get.fin, Vector.GetMul.eq.MulGet.fin]
    exact mul_comm a _
  have hrow (i : Fin n) : v * id (α := Tensor α [n]) X[i] = id (α := Tensor α [n]) X[i] * a := by
    apply Eq.of.All_EqGetS.fin
    intro j
    have hL : ((v * id (α := Tensor α [n]) X[i])[j] : Tensor α []) =
        (v[j] : Tensor α []) * ((id (α := Tensor α [n]) X[i])[j] : Tensor α []) :=
      GetMul.eq.MulGetS v (id (α := Tensor α [n]) X[i]) j
    have hR : ((id (α := Tensor α [n]) X[i] * a)[j] : Tensor α []) =
        ((id (α := Tensor α [n]) X[i])[j] : Tensor α []) * (a : α) :=
      GetMul.eq.MulGet.scalar (id (α := Tensor α [n]) X[i]) a j
    apply hL.trans
    have hvj : (v[j] : Tensor α []) = a0 :=
      EqGetStack.fin f j
    rw [hvj]
    refine Eq.trans ?_ hR.symm
    let tij : Tensor α [] := (id (α := Tensor α [n]) X[i])[j]
    have hsa : (id (α := Tensor α [n]) X[i])[j] * a = ⟨tij.data * a⟩ := by
      simp [tij, HMul.hMul]
      rfl
    rw [hsa]
    apply Eq.of.EqDataS
    simp [HMul.hMul, Mul.mul]
    apply Subtype.ext
    have ha0 : a0.data.val = [a] := rfl
    have hlen : ((id (α := Tensor α [n]) X[i])[j]).data.val.length = 1 :=
      (show [n].tail.prod = 1 from rfl) ▸ ((id (α := Tensor α [n]) X[i])[j]).data.property
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
    change List.zipWith Mul.mul a0.data.val ((id (α := Tensor α [n]) X[i])[j]).data.val =
      List.map (fun y => Mul.mul y a) tij.data.val
    rw [ha0, hx]
    simp [List.zipWith, List.map]
    exact mul_comm a x
  have hstack : ([_ < n] v) * X = X * a := by
    rw [MulStack.eq.Stack_Mul.fin X (fun _ : Fin n => v)]
    apply Eq.of.All_EqGetS.fin
    intro i
    have hL : (([i < n] (v * id (α := Tensor α [n]) X[i]))[i]) =
        v * id (α := Tensor α [n]) X[i] :=
      EqGetStack.fin (fun i : Fin n => v * id (α := Tensor α [n]) X[i]) i
    have hR : (X * a)[i] = X[i] * a :=
      GetMul.eq.MulGet.scalar X a i
    apply hL.trans
    apply (hrow i).trans
    exact hR.symm
  have hprod : (v.prod : Tensor α []) = (a : Tensor α []) ^ n := by
    apply Eq.trans (Prod_0.eq.Prod_Get v)
    apply Eq.trans
    · apply Finset.prod_congr rfl
      intro i _
      exact EqGetStack.fin f i
    · have hf : f = fun _ : Fin n => a0 := rfl
      rw [hf]
      apply Eq.trans (Finset.prod_const (s := Finset.univ) (b := a0))
      apply congrArg (fun k : ℕ => a0 ^ k)
      simp [Finset.card_univ, Fintype.card_fin]
  rw [hAX, ← hstack, DetMul.eq.MulProd v X, hprod]
  apply Eq.of.EqDataS
  apply Subtype.ext
  have hr : (a ^ n * X.det).data.val = ((a ^ n) * X.det.data).val :=
    congrArg (fun v => v.val) (DataMul.eq.Mul_Data (a ^ n) X.det)
  rw [hr]
  simp [HMul.hMul]
  cases hA : (a0 ^ n).data with
  | mk xs hxs =>
    cases hB : X.det.data with
    | mk ys hys =>
      simp
      have hxs' : xs = [a ^ n] := by
        have := congrArg (fun t : Tensor α [] => t.data.val) (Pow.eq.TensorListPow a n)
        rw [hA] at this
        exact this
      have hlen : ys.length = 1 := by
        have := X.det.data.property
        rw [hB] at this
        exact (show ([n, n].take ([n, n].length - 2)).prod = 1 from rfl) ▸ this
      obtain ⟨x, hys'⟩ := List.length_eq_one_iff.mp hlen
      erw [hA, hB]
      subst hxs'
      subst hys'
      simp [List.Vector.map]
      rfl


-- created on 2020-08-19
-- updated on 2026-09-07
