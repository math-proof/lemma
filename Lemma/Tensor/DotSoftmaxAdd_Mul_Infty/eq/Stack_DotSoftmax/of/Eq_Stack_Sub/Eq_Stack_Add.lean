import Lemma.Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmax
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.EqHeadData
import Lemma.Tensor.XEq.of.Eq
import Lemma.Vector.Head.eq.Get_0
open Tensor
set_option maxHeartbeats 4000000


@[main]
private lemma main
  [NeZero (l : ℕ)]
  [NeZero (u : ℕ)]
  [NeZero (n : ℕ)]
  {d_z : ℕ}
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
  have hβ (i : Fin n) :
      (([j < n] ((↑j + 1 - l : ℕ) : Tensor ℕ []))[i]).data[0] = ↑i + 1 - l := by
    have hi : ↑i < n := i.isLt
    refine
      (congrArg (fun t : Tensor ℕ [] => t.data[0])
        (EqGetStack.fin (n := n) (α := ℕ) (s := [])
          (fun j : Fin n => ((↑j + 1 - l : ℕ) : Tensor ℕ [])) ⟨↑i, hi⟩)) ▸ ?_
    apply Eq.trans (Vector.Get_0.eq.Head.fin ((↑(↑i + 1 - l) : Tensor ℕ []).data))
    apply EqHeadData.nat
  have hζ (i : Fin n) :
      (([j < n] ((↑j + u : ℕ) : Tensor ℕ []))[i]).data[0] = ↑i + u := by
    have hi : ↑i < n := i.isLt
    refine
      (congrArg (fun t : Tensor ℕ [] => t.data[0])
        (EqGetStack.fin (n := n) (α := ℕ) (s := [])
          (fun j : Fin n => ((↑j + u : ℕ) : Tensor ℕ [])) ⟨↑i, hi⟩)) ▸ ?_
    apply Eq.trans (Vector.Get_0.eq.Head.fin ((↑(↑i + u) : Tensor ℕ []).data))
    apply EqHeadData.nat
  have h := DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmax (l := l) (u := u) (n := n) (d_z := d_z) A V
  subst h_β h_ζ
  refine h.trans ?_
  apply XEq.symm
  apply Tensor.XEq.of.Eq
  let idxβ : Fin n → ℕ := fun i =>
    (([j < n] ((↑j + 1 - l : ℕ) : Tensor ℕ []))[i]).data[0]
  let idxζ : Fin n → ℕ := fun i =>
    (([j < n] ((↑j + u : ℕ) : Tensor ℕ []))[i]).data[0]
  let idxβ' : Fin n → ℕ := fun i => ↑i + 1 - l
  let idxζ' : Fin n → ℕ := fun i => ↑i + u
  change
    ([i < n]
      (map Hyperreal.ofReal A)[i][↑(idxβ i):↑(idxζ i)].softmax @
        (map Hyperreal.ofReal V)[↑(idxβ i):↑(idxζ i)]) =
      ([i < n]
        (map Hyperreal.ofReal A)[i][↑(idxβ' i):↑(idxζ' i)].softmax @
          (map Hyperreal.ofReal V)[↑(idxβ' i):↑(idxζ' i)])
  rw [show idxβ = idxβ' from funext hβ, show idxζ = idxζ' from funext hζ]


-- created on 2022-01-01
-- updated on 2026-08-28
