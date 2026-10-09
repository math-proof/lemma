import sympy.concrete.continuant
import sympy.sets.sets
import sympy.Basic
import Lemma.Finset.K_Add_1.eq.HFun
import Lemma.Finset.H_Add_1.eq.AddMul_K_Add_1KFun
import Lemma.Finset.H.gt.Zero.of.All_Imp_Gt_0
open Finset Continuant


@[path]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (_h₀ : n > 0)
  (h : ∀ i, x i > 0) :
-- imply
  K (fun i => x (i + 1)) n / H (fun i => x (i + 1)) n = H x (n + 1) / K x (n + 1) - x 0 := by
-- proof
  rw [K_Add_1.eq.HFun, H_Add_1.eq.AddMul_K_Add_1KFun, K_Add_1.eq.HFun]
  have hH := H.gt.Zero.of.All_Imp_Gt_0 (fun i => x (i + 1)) n (fun i _ => h (i + 1))
  field_simp
  ring


-- created on 2020-09-25
