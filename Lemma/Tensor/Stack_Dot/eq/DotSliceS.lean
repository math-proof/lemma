import sympy.Basic
import Mathlib.Data.Matrix.Mul


@[path]
private lemma main
  [NonUnitalNonAssocSemiring α]
  {n k : ℕ}
  {Q K : ℕ → Matrix (Fin n) (Fin n) α} :
-- imply
  (fun i : Fin k => Q i * K i) = fun i : Fin k => (fun j : Fin k => Q j) i * (fun j : Fin k => K j) i :=
-- proof
  rfl


-- created on 2020-08-17
