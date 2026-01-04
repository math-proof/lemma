import Lemma.Tensor.BandPart.eq.Stack_BoolIn_Icc
import Lemma.Tensor.EqGetS.of.Eq
import Lemma.Tensor.ExpAdd_MulInfty.eq.Mul_Stack_Bool
import Lemma.Tensor.Setoid.is.All_SetoidGetS
import sympy.matrices.expressions.special
open Tensor


@[main]
private lemma main
  [NeZero (l : ℕ)]
  [NeZero (u : ℕ)]
  [NeZero (n : ℕ)]
  [NeZero (d_z : ℕ)]
-- given
  (A : Tensor ℝ [n, n])
  (V : Tensor ℝ [n, d_z]) :
-- imply
  let Ξ := (1 : Tensor ℝ* [n, n]).band_part (l - 1) (u - 1)
  let A : Tensor ℝ* [n, n] := A
  let V : Tensor ℝ* [n, d_z] := V
  (A + (Ξ - 1) * ∞).softmax @ V ≈ [i < n] A[i, i + 1 - l : n ⊓ i + u].softmax @ V[i + 1 - l:n ⊓ i + u] := by
-- proof
  denote h_Ξ_def : Ξ = _
  denote h_A' : A' = _
  denote h_V' : V' = _
  have h_band_part := BandPart.eq.Stack_BoolIn_Icc n (l - 1) (u - 1) (α := ℝ*)
  have h_Ξ := ExpAdd_MulInfty.eq.Mul_Stack_Bool (fun i j => ((j - i : ℤ) ∈ Icc (-(l - 1 : ℕ) : ℤ) (u - 1 : ℕ) : Bool)) A
  rw [← h_band_part] at h_Ξ
  simp [← h_A', ← h_Ξ_def] at h_Ξ
  denote h_a' : a' = (A' + (Ξ - 1) * ∞)
  rw [← h_a'] at h_Ξ ⊢
  denote h_z : z = a'.softmax @ V'
  rw [← h_z]
  apply Setoid.of.All_SetoidGetS.fin
  intro i
  have h_zi := EqGetS.of.Eq.fin h_z i
  simp at h_zi
  sorry


-- created on 2026-01-02
-- updated on 2026-01-04
