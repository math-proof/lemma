module

public import Class.Analysis.SpecialFunctions.Exponential
public section


class Log (α : Type u) extends Zero α, One α, Div α where
  log : α → α
  log_zero : log 0 = 0
  log_one : log 1 = 0
  log_div_self (x : α) : log (x / x) = 0

class LogPos (α : Type u) extends Log α, ExpPos α where
  log_mul (h_x : x ≠ 0) (h_y : y ≠ 0) : log (x * y) = log x + log y
  log_div (h_x : x ≠ 0) (h_y : y ≠ 0) : log (x / y) = log x - log y
  log_exp (x : α) : log (exp x) = x
  exp_log_eq_abs (h : x ≠ 0) : exp (log x) = |x|
