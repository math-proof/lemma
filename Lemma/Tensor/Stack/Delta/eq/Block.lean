import sympy.functions.special.tensor_functions
import Lemma.Nat.Delta.eq.Ite
import Mathlib.Data.Real.Basic
open Nat


@[path]
private lemma main
  {m : ℕ} :
-- imply
  (fun j : Fin (m + 1) => (KroneckerDelta m (j : ℕ) : ℝ)) = Fin.append (0 : Fin m → ℝ) (fun _ : Fin 1 => 1) := by
-- proof
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  ·
    simp [Delta.eq.Ite, Nat.ne_of_gt i.isLt]
  ·
    fin_cases i
    simp [Delta.eq.Ite]


-- created on 2021-12-30
