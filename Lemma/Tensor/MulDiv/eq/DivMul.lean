import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Vector.GetMap.eq.UFnGet
import Lemma.Vector.GetMap₂.eq.BFnGetS
open Tensor Vector


/-- `(A / B) * C = (A * C) / B` for division by a 0-d tensor. -/
@[main]
private lemma main
  [Semifield α]
-- given
  (A C : Tensor α s)
  (B : Tensor α []) :
-- imply
  (A / B) * C = (A * C) / B := by
-- proof
  apply Eq.of.EqDataS
  apply Vector.Eq.of.All_EqGetS.fin
  intro i
  dsimp only [Mul.mul, HDiv.hDiv, HMul.hMul]
  erw [GetMap₂.eq.BFnGetS.fin]
  erw [GetMap.eq.UFnGet.fin (i := i)]
  erw [GetMap.eq.UFnGet.fin (i := i)]
  erw [GetMap₂.eq.BFnGetS.fin]
  apply div_mul_eq_mul_div


/-- `(a / B) * C = (a * C) / B` for scalar left factor. -/
@[main]
private lemma left
  [Semifield α]
-- given
  (a B : α)
  (C : Tensor α s) :
-- imply
  (a / B) * C = (a * C) / B := by
-- proof
  apply Eq.of.EqDataS
  apply Vector.Eq.of.All_EqGetS.fin
  intro i
  dsimp only [HMul.hMul, HDiv.hDiv]
  erw [GetMap.eq.UFnGet.fin (i := i)]
  erw [GetMap.eq.UFnGet.fin (i := i)]
  erw [GetMap.eq.UFnGet.fin (i := i)]
  apply div_mul_eq_mul_div


/-- `(A / B) * b = (A * b) / B` for scalar right factor. -/
@[main]
private lemma right
  [Semifield α]
-- given
  (A : Tensor α s)
  (b B : α) :
-- imply
  (A / B) * b = (A * b) / B := by
-- proof
  apply Eq.of.EqDataS
  apply Vector.Eq.of.All_EqGetS.fin
  intro i
  dsimp only [HMul.hMul, HDiv.hDiv]
  erw [GetMap.eq.UFnGet.fin (i := i)]
  erw [GetMap.eq.UFnGet.fin (i := i)]
  erw [GetMap.eq.UFnGet.fin (i := i)]
  erw [GetMap.eq.UFnGet.fin (i := i)]
  apply div_mul_eq_mul_div


-- created on 2026-08-12
