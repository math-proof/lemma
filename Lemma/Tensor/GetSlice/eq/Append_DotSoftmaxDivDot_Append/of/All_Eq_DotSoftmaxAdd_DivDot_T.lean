import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEqUFnS.of.SEq
import Lemma.List.EqSwap_0'1
import Lemma.Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmaxDivDot_T
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetSliceStack.as.Stack_UFn.of.Eq_Add
import Lemma.Tensor.MapStack.eq.Stack_Map
import Lemma.Tensor.SEqAppendS.of.SEq.SEq
import Lemma.Tensor.SEqDotS.of.SEq
import Lemma.Tensor.SEqTS.of.SEq
import Lemma.Tensor.Stack.eq.AppendStackS
import Lemma.Tensor.TAppend.as.AppendTS
import Lemma.Tensor.XEq.is.All_XEqGetS
import Lemma.Tensor.XEq.of.Eq
import Lemma.Tensor.XEqAppendS.of.XEq.XEq
open Bool List Tensor
set_option maxHeartbeats 800000


@[main]
private lemma kv_cache
  [NeZero (n : ℕ)]
  [NeZero (d_z : ℕ)]
-- given
  (Z : (n : ℕ) → Tensor ℝ [n, d_z])
  (Q K V : ℕ → Tensor ℝ [d_z])
  (h : ∀ (n : ℕ) [NeZero n],
    let Qn : Tensor ℝ* [n, d_z] := ([i < n] Q i : Tensor ℝ [n, d_z])
    let Kn : Tensor ℝ* [n, d_z] := ([i < n] K i : Tensor ℝ [n, d_z])
    let Vn : Tensor ℝ* [n, d_z] := ([i < n] V i : Tensor ℝ [n, d_z])
    let QK : Tensor ℝ* [n, n] := Qn @ Knᵀ
    (Z n : Tensor ℝ* [n, d_z]) ≈ (QK / √(d_z : ℝ*) + ((1 : Tensor ℝ* [n, n]).band_part n 0 - 1) * ∞).softmax @ Vn) :
-- imply
  let Kn : Tensor ℝ* [n, d_z] := ([i < n] K i : Tensor ℝ [n, d_z])
  let Vn : Tensor ℝ* [n, d_z] := ([i < n] V i : Tensor ℝ [n, d_z])
  let q : Tensor ℝ* [d_z] := Q n
  let k : Tensor ℝ* [d_z] := K n
  let v : Tensor ℝ* [d_z] := V n
  let KT : Tensor ℝ* ([d_z] ++ n :: []) := cast (congrArg (Tensor ℝ*) (EqSwap_0'1 n d_z)) Knᵀ
  let kT : Tensor ℝ* ([d_z] ++ 1 :: []) := cast (congrArg (Tensor ℝ*) (EqSwap_0'1 1 d_z)) ([_ < 1] k)ᵀ
  let row : Tensor ℝ* [d_z] := (q @ (KT ++ kT) / √(d_z : ℝ*)).softmax @ (Vn ++ [_ < 1] v)
  (Z (n + 1) : Tensor ℝ* [n + 1, d_z]) ≈ (Z n : Tensor ℝ* [n, d_z]) ++ [_ < 1] row := by
-- proof
  extract_lets Kn Vn q k v KT kT row
  let Qn : Tensor ℝ* [n, d_z] := ([i < n] Q i : Tensor ℝ [n, d_z])
  have hn1 := h (n + 1)
  have hgpt_succ := DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmaxDivDot_T.gpt ([i < n + 1] Q i) ([i < n + 1] K i) ([i < n + 1] V i)
  extract_lets Qs Ks Vs at hn1
  refine hn1.trans ?_
  refine hgpt_succ.trans ?_
  let f : ℕ → Tensor ℝ* [d_z] := fun i =>
    if hi : i < n + 1 then
      (Qs[i] @ Ks[:i + 1]ᵀ / √(d_z : ℝ*)).softmax @ Vs[:i + 1]
    else
      0
  have h_eq_f : [i < n + 1] (Qs[i] @ Ks[:i + 1]ᵀ / √(d_z : ℝ*)).softmax @ Vs[:i + 1] = [i < n + 1] f i := by
    apply Eq.of.All_EqGetS.fin
    intro i
    simp only [EqGetStack.fin]
    simp [f]
    split_ifs <;> grind
  refine (XEq.of.Eq (h_eq_f.trans (Stack.eq.AppendStackS (n := n) (j := 1) f))).trans ?_
  apply XEqAppendS.of.XEq.XEq
  ·
    have hn := h n
    apply XEq.of.All_XEqGetS
    intro i
    have hi : (i : ℕ) < n + 1 := Nat.lt_succ_of_lt i.isLt
    have hZ := hn.trans (DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmaxDivDot_T.gpt ([i < n] Q i) ([i < n] K i) ([i < n] V i))
    have hZi := All_XEqGetS.of.XEq hZ i
    refine (XEq.of.Eq ?eq).trans hZi.symm
    have hpre := EqGetStack.fun.fin f i
    have hgpti := EqGetStack.fin (fun j : Fin n => (Qn[j] @ Kn[:j + 1]ᵀ / √(d_z : ℝ*)).softmax @ Vn[:j + 1]) i
    have hrow : f i = (Qn[i] @ Kn[:i + 1]ᵀ / √(d_z : ℝ*)).softmax @ Vn[:i + 1] := by
      simp [f]
      apply Eq.of.SEq
      have hQ : Qs[i] = Qn[i] := by
        simp only [Qs, Qn]
        rw [MapStack.eq.Stack_Map, MapStack.eq.Stack_Map]
        have hQs := EqGetStack.fin (fun j : Fin (n + 1) => (Q j : Tensor ℝ* [d_z])) ⟨(i : ℕ), hi⟩
        have hQn := EqGetStack.fin (fun j : Fin n => (Q j : Tensor ℝ* [d_z])) i
        simp [GetElem.getElem] at hQs hQn ⊢
        exact hQs.trans hQn.symm
      have hK : Ks[:i + 1] ≃ Kn[:i + 1] := by
        have hKs : Ks = [t < n + 1] (K t : Tensor ℝ* [d_z]) := by
          simp only [Ks]
          rw [MapStack.eq.Stack_Map]
        have hKn : Kn = [t < n] (K t : Tensor ℝ* [d_z]) := by
          simp only [Kn]
          rw [MapStack.eq.Stack_Map]
        rw [hKs, hKn]
        exact (GetSliceStack.as.Stack_UFn.of.Eq_Add (by omega : n + 1 = ((i : ℕ) + 1) + (n - i)) (fun t => (K t : Tensor ℝ* [d_z]))).trans
          (GetSliceStack.as.Stack_UFn.of.Eq_Add (by omega : n = ((i : ℕ) + 1) + (n - ((i : ℕ) + 1))) (fun t => (K t : Tensor ℝ* [d_z]))).symm
      have hV : Vs[:i + 1] ≃ Vn[:i + 1] := by
        have hVs : Vs = [t < n + 1] (V t : Tensor ℝ* [d_z]) := by
          simp only [Vs]
          rw [MapStack.eq.Stack_Map]
        have hVn : Vn = [t < n] (V t : Tensor ℝ* [d_z]) := by
          simp only [Vn]
          rw [MapStack.eq.Stack_Map]
        rw [hVs, hVn]
        exact (GetSliceStack.as.Stack_UFn.of.Eq_Add (by omega : n + 1 = ((i : ℕ) + 1) + (n - i)) (fun t => (V t : Tensor ℝ* [d_z]))).trans
          (GetSliceStack.as.Stack_UFn.of.Eq_Add (by omega : n = ((i : ℕ) + 1) + (n - ((i : ℕ) + 1))) (fun t => (V t : Tensor ℝ* [d_z]))).symm
      refine (SEqDotS.of.SEq ?scores _).trans (SEqDotS.of.SEq.left hV _)
      refine SEqUFnS.of.SEq ?_ (fun {s} (t : Tensor ℝ* s) => t.softmax)
      refine SEqUFnS.of.SEq ?_ (fun {s} (t : Tensor ℝ* s) => t / √(d_z : ℝ*))
      refine (SEqDotS.of.SEq (SEq.of.Eq hQ) _).trans (SEqDotS.of.SEq.left (SEqTS.of.SEq hK) _)
    exact hpre.trans (hrow.trans hgpti.symm)
  ·
    apply XEq.of.All_XEqGetS
    intro i
    fin_cases i
    have hi : n < n + 1 := Nat.lt_succ_self n
    have hpre := EqGetStack.fin (fun j : Fin 1 => f (n + j)) ⟨0, Nat.zero_lt_one⟩
    have hrowg := EqGetStack.fin (fun _ : Fin 1 => row) ⟨0, Nat.zero_lt_one⟩
    have hrow : f n = row := by
      simp [f]
      apply Eq.of.SEq
      have hQ : Qs[n] = q := by
        simp only [Qs, q]
        rw [MapStack.eq.Stack_Map]
        have hQs := EqGetStack.fin (fun j : Fin (n + 1) => (Q j : Tensor ℝ* [d_z])) ⟨n, hi⟩
        simp [GetElem.getElem] at hQs ⊢
        exact hQs
      have hK : Ks[:n + 1]ᵀ ≃ KT ++ kT := by
        have hKs : Ks = [t < n + 1] (K t : Tensor ℝ* [d_z]) := by
          simp only [Ks]
          rw [MapStack.eq.Stack_Map]
        have hslice : Ks[:n + 1] ≃ [t < n + 1] (K t : Tensor ℝ* [d_z]) := by
          rw [hKs]
          exact GetSliceStack.as.Stack_UFn.of.Eq_Add (by omega : n + 1 = (n + 1) + 0) (fun t => (K t : Tensor ℝ* [d_z]))
        have happ : [t < n + 1] (K t : Tensor ℝ* [d_z]) ≃ Kn ++ [_ < 1] k := by
          have hKn : Kn = [t < n] (K t : Tensor ℝ* [d_z]) := by
            simp only [Kn]
            rw [MapStack.eq.Stack_Map]
          rw [hKn]
          rw [Stack.eq.AppendStackS (n := n) (j := 1) (fun t => (K t : Tensor ℝ* [d_z]))]
          apply SEqAppendS.of.SEq.SEq
          ·
            rfl
          ·
            apply SEq.of.Eq
            apply Eq.of.All_EqGetS.fin
            intro t
            fin_cases t
            simp only [EqGetStack.fin]
            simp [k]
        have ht : (Kn ++ [_ < 1] k)ᵀ ≃ KT ++ kT := by
          simp only [KT, kT]
          exact TAppend.as.AppendTS Kn ([_ < 1] k)
        exact (SEqTS.of.SEq (hslice.trans happ)).trans ht
      have hV : Vs[:n + 1] ≃ Vn ++ [_ < 1] v := by
        have hVs : Vs = [t < n + 1] (V t : Tensor ℝ* [d_z]) := by
          simp only [Vs]
          rw [MapStack.eq.Stack_Map]
        have hslice : Vs[:n + 1] ≃ [t < n + 1] (V t : Tensor ℝ* [d_z]) := by
          rw [hVs]
          exact GetSliceStack.as.Stack_UFn.of.Eq_Add (by omega : n + 1 = (n + 1) + 0) (fun t => (V t : Tensor ℝ* [d_z]))
        have happ : [t < n + 1] (V t : Tensor ℝ* [d_z]) ≃ Vn ++ [_ < 1] v := by
          have hVn : Vn = [t < n] (V t : Tensor ℝ* [d_z]) := by
            simp only [Vn]
            rw [MapStack.eq.Stack_Map]
          rw [hVn]
          rw [Stack.eq.AppendStackS (n := n) (j := 1) (fun t => (V t : Tensor ℝ* [d_z]))]
          apply SEqAppendS.of.SEq.SEq
          ·
            rfl
          ·
            apply SEq.of.Eq
            apply Eq.of.All_EqGetS.fin
            intro t
            fin_cases t
            simp only [EqGetStack.fin]
            simp [v]
        exact hslice.trans happ
      refine (SEqDotS.of.SEq ?row_scores _).trans (SEqDotS.of.SEq.left hV _)
      refine SEqUFnS.of.SEq ?_ (fun {s} (t : Tensor ℝ* s) => t.softmax)
      refine SEqUFnS.of.SEq ?_ (fun {s} (t : Tensor ℝ* s) => t / √(d_z : ℝ*))
      refine (SEqDotS.of.SEq (SEq.of.Eq hQ) _).trans (SEqDotS.of.SEq.left hK _)
    exact XEq.of.Eq (hpre.trans ((congrArg f (Nat.add_zero n)).trans (hrow.trans hrowg.symm)))


-- created on 2026-08-19
