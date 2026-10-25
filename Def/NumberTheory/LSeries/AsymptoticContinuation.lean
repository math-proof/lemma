/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AsymptoticContinuation.lean -/

import Def.NumberTheory.LSeries.AbelContinuation
import Lemma.Nat.LSeries.AbelContinuation
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
open Filter Asymptotics Topology


noncomputable section

/-- Linear asymptotic ansatz: pole part plus continuation of the remainder. -/
def linearAsymptoticDirichletContinuation (a : ℕ → ℂ) (ρ s : ℂ) : ℂ :=
  ρ * riemannZeta s + abelContinuation (fun n => a n - ρ) s

/-- Numerator of the linear asymptotic continuation cleared of denominators. -/
def linearAsymptoticNumerator (a : ℕ → ℂ) (ρ s : ℂ) : ℂ :=
  ρ * riemannZeta₁ s + (s - 1) * abelContinuation (fun n => a n - ρ) s

end
