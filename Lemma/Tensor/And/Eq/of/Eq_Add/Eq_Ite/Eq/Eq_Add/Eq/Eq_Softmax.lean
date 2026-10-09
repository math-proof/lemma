import sympy.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Matrix.Mul
import Mathlib.Logic.Equiv.Fin.Basic
open Matrix


/--
MegaByte: the patch embedding fed to the global model, the input of the local model and the conditional probability of every byte.
Bytes are indexed by \( t = k P + p \), and a patch is flattened by `finProdFinEquiv` : \( (a, b) \mapsto b + D_G a \).
Here \( K \) is the number of patches (\( K = \lceil T / P \rceil \) in the paper, but only the index bound \( t / P < K \) is used).
-/
@[path]
private lemma mega_byte
  {K' P' V DG DL : ℕ}
  {x : ℕ → Fin V}
  {E_global_embed : Fin V → Fin DG → ℝ}
  {E_pos : ℕ → Fin DG → ℝ}
  {E_global_pad : Fin ((P' + 1) * DG) → ℝ}
  {E_local_embed : Matrix (Fin V) (Fin DL) ℝ}
  {E_local_pad : Fin DL → ℝ}
  {w_GL : Matrix (Fin DG) (Fin DL) ℝ}
  {h_embed : ℕ → Fin DG → ℝ}
  {h_global_in h_global_out : Fin (K' + 1) → Fin ((P' + 1) * DG) → ℝ}
  {h_local_in h_local_out : Fin (K' + 1) → Fin (P' + 1) → Fin DL → ℝ}
  {transformer_global : (Fin (K' + 1) → Fin ((P' + 1) * DG) → ℝ) → Fin (K' + 1) → Fin ((P' + 1) * DG) → ℝ}
  {transformer_local : (Fin (P' + 1) → Fin DL → ℝ) → Fin (P' + 1) → Fin DL → ℝ}
  {Pr : ℕ → Fin V → ℝ}
-- given
  (_h_embed : ∀ t, h_embed t = E_global_embed (x t) + E_pos t)
  (h_global_in_def : ∀ (k : Fin (K' + 1)) (i : Fin ((P' + 1) * DG)),
    h_global_in k i =
      if k = 0 then
        E_global_pad i
      else
        h_embed ((k : ℕ) * (P' + 1) - (P' + 1) + (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2)
  (_h_global_out : h_global_out = transformer_global h_global_in)
  (h_local_in_def : ∀ (k : Fin (K' + 1)) (p : Fin (P' + 1)) (a : Fin DL),
    h_local_in k p a =
      Matrix.vecMul (fun g : Fin DG => h_global_out k (finProdFinEquiv (p, g))) w_GL a +
        if p = 0 then
          E_local_pad a
        else
          E_local_embed (x ((k : ℕ) * (P' + 1) + p - 1)) a)
  (_h_local_out : ∀ k, h_local_out k = transformer_local (h_local_in k))
  (h_prob : ∀ (k : Fin (K' + 1)) (p : Fin (P' + 1)),
    Pr ((k : ℕ) * (P' + 1) + p) = fun b => Real.exp ((E_local_embed *ᵥ h_local_out k p) b) / ∑ c, Real.exp ((E_local_embed *ᵥ h_local_out k p) c)) :
-- imply
  h_global_in = Fin.cons E_global_pad (fun (k : Fin K') (i : Fin ((P' + 1) * DG)) => h_embed ((k : ℕ) * (P' + 1) + (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2) ∧
  (∀ k : Fin (K' + 1),
    h_local_in k = fun (p : Fin (P' + 1)) (a : Fin DL) =>
      Matrix.vecMul (fun g : Fin DG => h_global_out k (finProdFinEquiv (p, g))) w_GL a +
        (Fin.cons E_local_pad (fun (p : Fin P') => E_local_embed (x ((k : ℕ) * (P' + 1) + p))) : Fin (P' + 1) → Fin DL → ℝ) p a) ∧
  (∀ (t : ℕ) (hk : t / (P' + 1) < K' + 1),
    Pr t (x t) =
      Real.exp ((E_local_embed *ᵥ h_local_out ⟨t / (P' + 1), hk⟩ ⟨t % (P' + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩) (x t)) /
        ∑ c, Real.exp ((E_local_embed *ᵥ h_local_out ⟨t / (P' + 1), hk⟩ ⟨t % (P' + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩) c)) := by
-- proof
  refine ⟨?_, ?_, ?_⟩
  ·
    funext k i
    refine Fin.cases ?_ (fun k' => ?_) k
    ·
      simp [h_global_in_def]
    ·
      simp [h_global_in_def]
      have h : ((k' : ℕ) + 1) * (P' + 1) - (P' + 1) = (k' : ℕ) * (P' + 1) := by
        rw [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel]
      rw [h]
  ·
    intro k
    funext p a
    rw [h_local_in_def]
    refine Fin.cases ?_ (fun p' => ?_) p
    ·
      simp
    ·
      simp
  ·
    intro t hk
    have h := congrFun (h_prob ⟨t / (P' + 1), hk⟩ ⟨t % (P' + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩) (x t)
    have ht : t / (P' + 1) * (P' + 1) + t % (P' + 1) = t := by
      rw [Nat.mul_comm]
      exact Nat.div_add_mod t (P' + 1)
    simpa [ht] using h


-- created on 2023-06-04
