/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AsymptoticContinuation.lean -/

module

public import Def.NumberTheory.LSeries.AbelContinuation
public import Theorem.Nat.LSeries.AbelContinuation
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp

@[expose] public section

open Filter Asymptotics Topology


noncomputable section

/-- Linear asymptotic ansatz: pole part plus continuation of the remainder. -/
def linearAsymptoticDirichletContinuation (a : ℕ → ℂ) (ρ s : ℂ) : ℂ :=
  ρ * riemannZeta s + abelContinuation (fun n => a n - ρ) s

/-- Numerator of the linear asymptotic continuation cleared of denominators. -/
def linearAsymptoticNumerator (a : ℕ → ℂ) (ρ s : ℂ) : ℂ :=
  ρ * riemannZeta₁ s + (s - 1) * abelContinuation (fun n => a n - ρ) s

end
