import Def.LanglandsTunnell_CubicInduction_ArchSmooth3

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField AutomorphicForm

namespace LanglandsTunnell.CubicInduction.WhittakerBlock

def archDeriv (i j : Fin 3) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ :=
  fun g => deriv (fun s : ℝ => φ (g * WhittakerBlock.archRealLift3 fun a b =>
    (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0)) 0

def casimir1 (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ :=
  fun g => ∑ i : Fin 3, archDeriv i i φ g

def casimir2 (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ :=
  fun g => ∑ i : Fin 3, ∑ j : Fin 3, archDeriv i j (archDeriv j i φ) g

def casimir3 (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ :=
  fun g => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, archDeriv i j (archDeriv j k (archDeriv k i φ)) g

def IsCentreFinite (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Prop :=
  (∃ (N : ℕ) (a : Fin (N + 1) → ℂ), a (Fin.last N) = 1 ∧ ∑ m, a m • (casimir1^[m] φ) = 0) ∧
    (∃ (N : ℕ) (a : Fin (N + 1) → ℂ), a (Fin.last N) = 1 ∧ ∑ m, a m • (casimir2^[m] φ) = 0) ∧
      ∃ (N : ℕ) (a : Fin (N + 1) → ℂ), a (Fin.last N) = 1 ∧ ∑ m, a m • (casimir3^[m] φ) = 0

end LanglandsTunnell.CubicInduction.WhittakerBlock
