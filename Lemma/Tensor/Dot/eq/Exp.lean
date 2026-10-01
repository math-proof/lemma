import sympy.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
open Matrix


@[main]
private lemma main
  {k m : ℕ}
  {A : Matrix (Fin k) (Fin m) ℂ}
  {B : Fin m → ℂ} :
-- imply
  A.map Complex.exp *ᵥ (fun j => Complex.exp (B j)) = fun i => ∑ j, Complex.exp (A i j + B j) := by
-- proof
  funext i
  simp [Matrix.mulVec, dotProduct, Complex.exp_add]


-- created on 2020-11-11
