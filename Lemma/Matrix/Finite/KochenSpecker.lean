import Mathlib
import sympy.Basic
import sympy.atlas.QuantumInformation.Finite.KochenSpecker
open MathlibExt.QuantumInformation.Finite.KochenSpeckerWanted


/--
[kochen_specker_finite_real_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/KochenSpecker.lean)
-/
@[path]
private lemma kochen_specker_finite_real_three_eq
  :
-- imply
  ∃ (N : ℕ) (v : Fin N → EuclideanSpace ℝ (Fin 3)),
    (∀ i, ‖v i‖ = 1) ∧
    ¬ ∃ (c : Fin N → Fin 2),
    (∀ i j : Fin N, inner (𝕜 := by
-- proof
  apply MathlibExt.QuantumInformation.Finite.KochenSpeckerWanted.kochen_specker_finite_real_three


-- created on 2026-10-20
