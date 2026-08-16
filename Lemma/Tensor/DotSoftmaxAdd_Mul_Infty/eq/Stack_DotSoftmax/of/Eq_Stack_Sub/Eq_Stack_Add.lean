import Lemma.Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmax
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.XEq.of.Eq
open Tensor


@[main]
private lemma main
  [NeZero (l : ℕ)]
  [NeZero (u : ℕ)]
  [NeZero (n : ℕ)]
  [NeZero (d_z : ℕ)]
  {β ζ : Tensor ℕ [n]}
-- given
  (h_β : β = [i < n] (i + 1 - l : ℕ))
  (h_ζ : ζ = [i < n] (i + u : ℕ))
  (A : Tensor ℝ [n, n])
  (V : Tensor ℝ [n, d_z]) :
-- imply
  let Ξ := (1 : Tensor ℝ* [n, n]).band_part (l - 1) (u - 1)
  let A : Tensor ℝ* [n, n] := A
  let V : Tensor ℝ* [n, d_z] := V
  (A + (Ξ - 1) * ∞).softmax @ V ≈ [i < n]
    let βᵢ := β[i].data[0]
    let ζᵢ := ζ[i].data[0]
    A[i, βᵢ: ζᵢ].softmax @ V[βᵢ: ζᵢ] := by
-- proof
  have h := DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmax (l := l) (u := u) (n := n) (d_z := d_z) A V
  subst h_β h_ζ
  refine h.trans ?_
  apply XEq.symm
  apply XEq.of.Eq
  apply Eq.of.All_EqGetS.fin
  intro i
  rw [EqGetStack.fn.fin, EqGetStack.fn.fin]
  have hβ : (([j < n] ((j.val + 1 - l : ℕ) : Tensor ℕ []))[i]).data[0] = i + 1 - l := by
    simp [GetElem.getElem]
    erw [EqGetStack.fn.fin]
    rfl
  have hζ : (([j < n] ((j.val + u : ℕ) : Tensor ℕ []))[i]).data[0] = i + u := by
    simp [GetElem.getElem]
    erw [EqGetStack.fn.fin]
    rfl
  rw [hβ, hζ]


-- created on 2022-01-01
