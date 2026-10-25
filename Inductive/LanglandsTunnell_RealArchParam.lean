import Mathlib
set_option autoImplicit false


namespace LanglandsTunnell

inductive RealArchParam where
  | principal (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) : RealArchParam
  | discrete (u : ℂ) (k : ℕ) (hk : 1 ≤ k) : RealArchParam

end LanglandsTunnell
