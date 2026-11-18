module

public import Instance.Analysis.SpecialFunctions.Exponential.Part4
public section
open Filter Hyperreal Int

class LogPos (α : Type u) extends Log α, ExpPos α where
  log_mul (h_x : x ≠ 0) (h_y : y ≠ 0) : log (x * y) = log x + log y
  log_div (h_x : x ≠ 0) (h_y : y ≠ 0) : log (x / y) = log x - log y
  log_exp (x : α) : log (exp x) = x
  exp_log_eq_abs (h : x ≠ 0) : exp (log x) = |x|

