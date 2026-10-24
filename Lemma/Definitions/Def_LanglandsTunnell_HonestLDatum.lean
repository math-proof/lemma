import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

noncomputable section

open Complex Polynomial

namespace LanglandsTunnell

structure LDatum (ι : Type*) where

  norm : ι → ℕ

  euler : ι → ℂ[X]

  dual : ι → ℂ[X]

  gammaR : Multiset ℂ

  gammaC : Multiset ℂ

  gammaRDual : Multiset ℂ

  gammaCDual : Multiset ℂ

  abscissa : ℝ

  center : ℝ

  degree : ℕ

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

def badFactor (bad : Multiset (ℕ × ℂ[X])) (s : ℂ) : ℂ :=
  (bad.map fun x => x.2.eval ((x.1 : ℂ) ^ (-s))).prod

def IsBadData (bad : Multiset (ℕ × ℂ[X])) : Prop :=
  ∀ x ∈ bad, 2 ≤ x.1 ∧ x.2.coeff 0 = 1

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

def IsNice : Prop :=
  D.WellFormed ∧ D.Converges ∧
  ∃ (bad badDual : Multiset (ℕ × ℂ[X])) (ε : ℂ) (N : ℝ) (Λ Λd : ℂ → ℂ),
    IsBadData bad ∧ IsBadData badDual ∧ 0 < N ∧
    Differentiable ℂ Λ ∧ Differentiable ℂ Λd ∧
    BoundedOnStrips Λ ∧ BoundedOnStrips Λd ∧
    (∀ s : ℂ, D.abscissa < s.re → Λ s * badFactor bad s = D.archFactor s * D.LFun s) ∧
    (∀ s : ℂ, D.abscissa < s.re →
      Λd s * badFactor badDual s = D.archFactorDual s * D.LFunDual s) ∧
    (∀ s : ℂ, Λ s = ε * (N : ℂ) ^ ((D.center : ℂ) - s) * Λd (2 * (D.center : ℂ) - s))

@[simp] theorem badFactor_zero (s : ℂ) : badFactor 0 s = 1 := by
  simp [badFactor]

theorem isBadData_zero : IsBadData 0 := fun _ h => (Multiset.notMem_zero _ h).elim

theorem archFactor_of_gammaC_eq_zero (hC : D.gammaC = 0) (s : ℂ) :
    D.archFactor s = (D.gammaR.map fun μ => Gammaℝ (s + μ)).prod := by
  simp [archFactor, hC]

end LDatum

end LanglandsTunnell

end
