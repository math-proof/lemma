import Lemma.Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmaxDivDot_T
import Lemma.Tensor.GetSliceStack.as.Stack_UFnAdd.of.Eq
import Lemma.Tensor.SEqAppendS.of.SEq.SEq
import Lemma.Tensor.SEqGetSliceSStack.of.LengthSlice
import Lemma.Tensor.Stack.eq.AppendStackS
import Lemma.Tensor.TAppend.as.AppendTS
import Lemma.Tensor.XEqAppendS.of.XEq.XEq
open Tensor
set_option maxHeartbeats 1000000


@[main]
private lemma kv_cache
  [NeZero (l : ℕ)]
  {n : ℕ}
  {d_z : ℕ}
  {Z : (n : ℕ) → Tensor ℝ [n, d_z]}
  {Q K V : ℕ → Tensor ℝ [d_z]}
-- given
  (h : ∀ n,
    let Qn : Tensor ℝ* [n, d_z] := ([i < n] Q i : Tensor ℝ [n, d_z])
    let Kn : Tensor ℝ* [n, d_z] := ([i < n] K i : Tensor ℝ [n, d_z])
    let Vn : Tensor ℝ* [n, d_z] := ([i < n] V i : Tensor ℝ [n, d_z])
    let QK : Tensor ℝ* [n, n] := Qn @ Knᵀ
    (Z n : Tensor ℝ* [n, d_z]) ≈ (QK / √(d_z : ℝ*) + ((1 : Tensor ℝ* [n, n]).band_part (l - 1) 0 - 1) * ∞).softmax @ Vn) :
-- imply
  let Kn : Tensor ℝ* [n, d_z] := ([i < n] K i : Tensor ℝ [n, d_z])
  let Vn : Tensor ℝ* [n, d_z] := ([i < n] V i : Tensor ℝ [n, d_z])
  let Kw : Tensor ℝ* [((⟨(n + 1 - l : ℕ), n, 1⟩ : Slice).length n), d_z] := Kn[(n + 1 - l : ℕ):n]
  let Vw : Tensor ℝ* [((⟨(n + 1 - l : ℕ), n, 1⟩ : Slice).length n), d_z] := Vn[(n + 1 - l : ℕ):n]
  let KT : Tensor ℝ* ([d_z] ++ Kw.length :: []) := cast (congrArg (Tensor ℝ*) (List.EqSwap_0'1 Kw.length d_z)) Kwᵀ
  let kT : Tensor ℝ* ([d_z] ++ 1 :: []) := cast (congrArg (Tensor ℝ*) (List.EqSwap_0'1 1 d_z)) ([_ < 1] (K n : Tensor ℝ* [d_z]))ᵀ
  let row : Tensor ℝ* [d_z] := ((Q n : Tensor ℝ* [d_z]) @ (KT ++ kT) / √(d_z : ℝ*)).softmax @ (Vw ++ [_ < 1] (V n : Tensor ℝ* [d_z]))
  (Z (n + 1) : Tensor ℝ* [n + 1, d_z]) ≈ (Z n : Tensor ℝ* [n, d_z]) ++ [_ < 1] row := by
-- proof
  extract_lets Kn Vn Kw Vw KT kT row
  let Qn : Tensor ℝ* [n, d_z] := ([i < n] Q i : Tensor ℝ [n, d_z])
  have hn1 := h (n + 1)
  extract_lets Qs Ks Vs at hn1
  apply hn1.trans
  apply (DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmaxDivDot_T.gpt ([i < n + 1] Q i) ([i < n + 1] K i) ([i < n + 1] V i)).trans
  let f : ℕ → Tensor ℝ* [d_z] := fun i =>
    if hi : i < n + 1 then
      (Qs[i] @ Ks[(i + 1 - l : ℕ):(i + 1 : ℕ)]ᵀ / √(d_z : ℝ*)).softmax @ Vs[(i + 1 - l : ℕ):(i + 1 : ℕ)]
    else
      0
  apply XEq.trans (b := [i < n] f i ++ [i < 1] f (n + i))
  ·
    apply XEq.of.Eq
    apply Eq.trans (b := [i < n + 1] f i)
    ·
      apply Eq.of.All_EqGetS.fin
      intro i
      simp only [EqGetStack.fin]
      simp [f]
      erw [EqGetStack.fin]
      split_ifs
      .
        aesop
      .
        omega
    ·
      apply Stack.eq.AppendStackS
  apply XEqAppendS.of.XEq.XEq
  ·
    apply XEq.of.All_XEqGetS
    intro i
    apply (XEq.of.Eq _).trans (All_XEqGetS.of.XEq ((h n).trans (DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmaxDivDot_T.gpt ([i < n] Q i) ([i < n] K i) ([i < n] V i))) i).symm
    apply (EqGetStack.fun.fin f i).trans
    apply Eq.trans (b := (Qn[i] @ Kn[((i : ℕ) + 1 - l : ℕ):((i : ℕ) + 1 : ℕ)]ᵀ / √(d_z : ℝ*)).softmax @ Vn[((i : ℕ) + 1 - l : ℕ):((i : ℕ) + 1 : ℕ)])
    ·
      simp [f]
      apply Bool.Eq.of.SEq
      apply (SEqDotS.of.SEq _ _).trans (SEqDotS.of.SEq.left _ _)
      ·
        apply Bool.SEqUFnS.of.SEq _ (fun {s} (t : Tensor ℝ* s) => t.softmax)
        apply Bool.SEqUFnS.of.SEq _ (fun {s} (t : Tensor ℝ* s) => t / √(d_z : ℝ*))
        apply (SEqDotS.of.SEq (Bool.SEq.of.Eq _) _).trans (SEqDotS.of.SEq.left _ _)
        ·
          simp only [Qs, Qn]
          repeat rw [MapStack.eq.Stack_Map]
          simp [GetElem.getElem]
          repeat erw [EqGetStack.fin]
        ·
          apply SEqTS.of.SEq
          simp only [Ks, Kn]
          repeat rw [MapStack.eq.Stack_Map]
          apply SEqGetSliceSStack.of.LengthSlice (f := fun t => (K t : Tensor ℝ* [d_z]))
          simp only [List.LengthSlice.eq.SubMin]
          grind
      ·
        simp only [Vs, Vn]
        repeat rw [MapStack.eq.Stack_Map]
        apply SEqGetSliceSStack.of.LengthSlice (f := fun t => (V t : Tensor ℝ* [d_z]))
        simp only [List.LengthSlice.eq.SubMin]
        grind
    ·
      symm
      apply EqGetStack.fin
  ·
    apply XEq.of.All_XEqGetS
    intro i
    fin_cases i
    apply XEq.of.Eq
    apply (EqGetStack.fin (fun j : Fin 1 => f (n + j)) ⟨0, Nat.zero_lt_one⟩).trans
    apply (congrArg f (Nat.add_zero n)).trans
    have := NeZero.pos l
    trans row
    ·
      simp [f]
      apply Bool.Eq.of.SEq
      apply (SEqDotS.of.SEq _ _).trans (SEqDotS.of.SEq.left _ _)
      ·
        apply Bool.SEqUFnS.of.SEq _ (fun {s} (t : Tensor ℝ* s) => t.softmax)
        apply Bool.SEqUFnS.of.SEq _ (fun {s} (t : Tensor ℝ* s) => t / √(d_z : ℝ*))
        apply (SEqDotS.of.SEq (Bool.SEq.of.Eq _) _).trans (SEqDotS.of.SEq.left _ _)
        ·
          simp only [Qs]
          rw [MapStack.eq.Stack_Map]
          simp [GetElem.getElem]
          apply EqGetStack.fin
        ·
          apply SEq.trans (b := (Kw ++ [_ < 1] (K n : Tensor ℝ* [d_z]))ᵀ)
          ·
            apply SEqTS.of.SEq
            simp only [Ks]
            rw [MapStack.eq.Stack_Map]
            apply (GetSliceStack.as.Stack_UFnAdd.of.Eq
              (n := n + 1) (start := n + 1 - l) (stop := n + 1) (k := n - (n + 1 - l) + 1)
              (by rw [List.LengthSlice.eq.SubMin]; grind)
              (fun t => (K t : Tensor ℝ* [d_z]))).trans
            apply (Bool.SEq.of.Eq (Stack.eq.AppendStackS (fun t => (K (t + (n + 1 - l)) : Tensor ℝ* [d_z])))).trans
            apply SEqAppendS.of.SEq.SEq
            ·
              simp only [Kw, Kn]
              rw [MapStack.eq.Stack_Map]
              apply (GetSliceStack.as.Stack_UFnAdd.of.Eq
                (by rw [List.LengthSlice.eq.SubMin]; grind)
                (fun t => (K t : Tensor ℝ* [d_z]))).symm
            ·
              apply Bool.SEq.of.Eq
              apply Eq.of.All_EqGetS.fin
              intro t
              fin_cases t
              grind [EqGetStack.fin]
          ·
            simp only [KT, kT]
            apply TAppend.as.AppendTS
      ·
        apply SEq.trans (b := Vw ++ [_ < 1] (V n : Tensor ℝ* [d_z]))
        ·
          simp only [Vs]
          rw [MapStack.eq.Stack_Map]
          apply (GetSliceStack.as.Stack_UFnAdd.of.Eq
            (n := n + 1) (start := n + 1 - l) (stop := n + 1) (k := n - (n + 1 - l) + 1)
            (by rw [List.LengthSlice.eq.SubMin]; grind)
            (fun t => (V t : Tensor ℝ* [d_z]))).trans
          apply (Bool.SEq.of.Eq (Stack.eq.AppendStackS (fun t => (V (t + (n + 1 - l)) : Tensor ℝ* [d_z])))).trans
          apply SEqAppendS.of.SEq.SEq
          ·
            simp only [Vw, Vn]
            rw [MapStack.eq.Stack_Map]
            apply (GetSliceStack.as.Stack_UFnAdd.of.Eq
              (by rw [List.LengthSlice.eq.SubMin]; grind)
              (fun t => (V t : Tensor ℝ* [d_z]))).symm
          ·
            apply Bool.SEq.of.Eq
            apply Eq.of.All_EqGetS.fin
            intro t
            fin_cases t
            grind [EqGetStack.fin]
        ·
          apply Bool.SEq.of.Eq
          rfl
    ·
      symm
      apply EqGetStack.fin


-- created on 2026-08-19
-- updated on 2026-08-20
