import Mathlib
set_option autoImplicit false


namespace IncidenceSystem

inductive Var (g e m' : ℕ) : Type
  | u : Fin g → Var g e m'
  | w : Fin g → Fin e → Fin (m' + 1) → Var g e m'
  | σ : Option (Fin (g * m')) → Fin g → Fin (m' + 1) → Var g e m'
  | c : Fin (g * m') → Var g e m'
  deriving DecidableEq, Fintype

end IncidenceSystem
