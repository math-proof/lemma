import Lemma.Hyperreal.UFn.of.All_UFn
import Lemma.Int.Abs.eq.Max_Neg
import Instance.Analysis.SpecialFunctions.Exponential.Part3
open Filter Hyperreal Int


class Log (α : Type u) extends Zero α, One α, Div α where
  log : α → α
  log_zero : log 0 = 0
  log_one : log 1 = 0
  log_div_self (x : α) : log (x / x) = 0

