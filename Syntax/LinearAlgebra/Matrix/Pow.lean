import Mathlib.Data.Matrix.Basic


/-- `α ^ [m, n]` expands to `Matrix (Fin m) (Fin n) α`. -/
syntax:80 (name := matrixPowShape) (priority := high)
  term:81 " ^ " "[" term:60 ", " term:60 "]" : term

macro_rules (kind := matrixPowShape)
  | `($α ^ [$m, $n]) => `(Matrix (Fin $m) (Fin $n) $α)
