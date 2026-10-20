import Mathlib
import sympy.Basic
import sympy.atlas.QuantumInformation.Finite.TsirelsonTight
open Matrix
open MathlibExt.QuantumInformation.Finite.TsirelsonTight


/--
[tsirelson_bound_tight](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma tsirelson_bound_tight_eq
  :
-- imply
  ∃ (A₀ A₁ B₀ B₁ : Matrix (Fin 4) (Fin 4) ℂ),
    IsCHSHTuple A₀ A₁ B₀ B₁ ∧
    Module.End.HasEigenvalue
    (Matrix.toLin' (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁))
    ((↑(2 * Real.sqrt 2) : ℂ)) := by
-- proof
  apply MathlibExt.QuantumInformation.Finite.TsirelsonTight.tsirelson_bound_tight


-- created on 2026-10-20
