import Lemma.Definitions.Def_LanglandsTunnell_JLConverse

set_option autoImplicit false

noncomputable section

open Complex LanglandsTunnell.Converse.ArchR

namespace LanglandsTunnell.Converse

namespace PrincipalFamily

def phiStd (a : ZMod 2) (v : ℝ) : ℂ :=
  (if a = 0 then 1 else (v : ℂ)) * (Real.exp (-Real.pi * v ^ 2) : ℂ)

def innerW (a₁ a₂ : ZMod 2) (h : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) : ℂ :=
  ∫ x : ℝ, phiStd a₁ (-(t * (h 0 0 + x * h 1 0))) * phiStd a₂ (-(t * (h 0 1 + x * h 1 1))) * psi (-x)

def Wmem (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (g : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  ((|g.det| : ℝ) : ℂ) * quasiChar u₁ a₁ g.det * ∫ t : ℝ, innerW a₁ a₂ g t * quasiChar (u₁ - u₂) (a₁ + a₂) t

end PrincipalFamily

namespace DiscreteFamily

def nsq (g : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := g 1 0 ^ 2 + g 1 1 ^ 2

def iy (g : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := g.det / nsq g

def ix (g : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := (g 0 0 * g 1 0 + g 0 1 * g 1 1) / nsq g

def kap (g : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := ((g 1 1 : ℂ) - (g 1 0 : ℂ) * I) / (Real.sqrt (nsq g) : ℂ)

def pexp (k₀ : ℕ) : ℝ := (k₀ : ℝ) / 2 + 1

def prof (k₀ : ℕ) (y : ℝ) : ℝ := y ^ pexp k₀ * Real.exp (-(2 * Real.pi * y))

def detPow (u₀ : ℂ) (g : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := Complex.exp (u₀ * (Real.log g.det : ℂ))

def W (u₀ : ℂ) (k₀ : ℕ) (g : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  if 0 < g.det then
    psi (ix g) * (prof k₀ (iy g) : ℂ) * kap g ^ (k₀ + 1) * (Real.sqrt (nsq g) : ℂ) * detPow u₀ g
  else 0

end DiscreteFamily

end LanglandsTunnell.Converse

end
