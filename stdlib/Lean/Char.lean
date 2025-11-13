import Lean

/--
check whether the char is within range ₀₁₂₃₄₅₆₇₈₉
-/
def Char.isSubscriptDigit (c : Char) : Bool :=
  c ≥ '₀' && c ≤ '₉'

def Char.transformExpr (s₀ : Char) (s : List Char) : List Char :=
  if s₀ == '_' then
    s
  else
    -- s.match(/^[A-Z][\w'!₀-₉]+?S/)
    let plural :=
      if s₀.isUpper then
        match s.dropWhile fun c => c != 'S' && (c.isAlphanum || c == '\'' || c == '!' || c.isSubscriptDigit) with
        | 'S' :: _ =>
          true
        | _ =>
          false
      else
        false
    if plural then s₀ :: s else '_' :: s₀ :: s
