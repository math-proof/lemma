import sympy.Basic
import Mathlib.Analysis.SpecialFunctions.Exp


@[main]
private lemma main
  {a b n : ℕ}
  {A : Fin a → Fin n → ℝ}
  {B : Fin b → Fin n → ℝ} :
-- imply
  (fun i j => Real.exp (Fin.append A B i j)) = Fin.append (fun i j => Real.exp (A i j)) (fun i j => Real.exp (B i j)) := by
-- proof
  funext i
  exact Fin.addCases (fun i => by simp) (fun i => by simp) i


-- created on 2026-09-27
