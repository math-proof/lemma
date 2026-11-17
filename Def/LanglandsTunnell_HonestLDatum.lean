module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Structure.LanglandsTunnell_HonestLDatum

@[expose] public section

noncomputable section

open Complex Polynomial

namespace LanglandsTunnell

namespace LDatum

variable {ι : Type*} (D : LDatum ι)

def LFun (s : ℂ) : ℂ :=
  ∏' i, ((D.euler i).eval ((D.norm i : ℂ) ^ (-s)))⁻¹

def LFunDual (s : ℂ) : ℂ :=
  ∏' i, ((D.dual i).eval ((D.norm i : ℂ) ^ (-s)))⁻¹

def archFactor (s : ℂ) : ℂ :=
  (D.gammaR.map fun μ => Gammaℝ (s + μ)).prod * (D.gammaC.map fun μ => Gammaℂ (s + μ)).prod

def archFactorDual (s : ℂ) : ℂ :=
  (D.gammaRDual.map fun μ => Gammaℝ (s + μ)).prod *
    (D.gammaCDual.map fun μ => Gammaℂ (s + μ)).prod

def WellFormed : Prop :=
  (∀ i, 2 ≤ D.norm i) ∧
  (∀ i, (D.euler i).coeff 0 = 1 ∧ (D.euler i).natDegree ≤ D.degree ∧
    (D.dual i).coeff 0 = 1 ∧ (D.dual i).natDegree ≤ D.degree) ∧
  (∀ μ ∈ D.gammaR, -μ.re ≤ D.abscissa) ∧ (∀ μ ∈ D.gammaC, -μ.re ≤ D.abscissa) ∧
  (∀ μ ∈ D.gammaRDual, -μ.re ≤ D.abscissa) ∧ (∀ μ ∈ D.gammaCDual, -μ.re ≤ D.abscissa)

def Converges : Prop :=
  ∀ s : ℂ, D.abscissa < s.re →
    Summable (fun i => ‖(D.euler i).eval ((D.norm i : ℂ) ^ (-s)) - 1‖) ∧
    Summable (fun i => ‖(D.dual i).eval ((D.norm i : ℂ) ^ (-s)) - 1‖) ∧
    D.LFun s ≠ 0 ∧ D.LFunDual s ≠ 0

def BoundedOnStrips (Λ : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖Λ s‖ ≤ C

end LDatum

end LanglandsTunnell

end
