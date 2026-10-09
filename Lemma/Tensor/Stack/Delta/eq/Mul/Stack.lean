import sympy.functions.special.tensor_functions
import Lemma.Nat.Delta.eq.Ite
import Mathlib.Data.Real.Basic
open Nat


@[path]
private lemma main
  {n i d : ℕ}
  {f : ℕ → ℝ} :
-- imply
  (fun j : Fin n => (KroneckerDelta i (j + d) : ℝ) * f j) = fun j : Fin n => f (i - d) * KroneckerDelta i (j + d) := by
-- proof
  funext j
  rw [Delta.eq.Ite]
  split_ifs with h
  ·
    subst h
    simp
  ·
    simp


-- created on 2021-12-30
