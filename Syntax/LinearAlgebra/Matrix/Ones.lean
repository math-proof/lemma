import Mathlib.Data.Matrix.Basic


/-- All-ones matrix `𝟙[m, n] : Matrix (Fin m) (Fin n) ℕ`. -/
syntax:max "𝟙[" term:60 ", " term:60 "]" : term

macro_rules
  | `(𝟙[$m, $n]) => `(Matrix.of fun (_ : Fin $m) (_ : Fin $n) => (1 : ℕ))
