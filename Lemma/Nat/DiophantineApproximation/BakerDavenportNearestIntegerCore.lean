import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.DiophantineApproximation.BakerDavenportNearestIntegerCore
open MetaMathlibExt


/--
[nearestInteger_reduction_core](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DiophantineApproximation/BakerDavenportNearestIntegerCore.lean)
-/
@[path]
private lemma nearestInteger_reduction_core_eq
  {q M u : ℕ}
  {kappa mu : ℝ}
  {v : ℤ}
  {epsilon : ℝ}
-- given
  (hu : u ≤ M)
  (heq : epsilon = |mu * (q : ℝ) - (round (mu * (q : ℝ)) : ℝ)| - (M : ℝ) * |kappa * (q : ℝ) - (round (kappa * (q : ℝ)) : ℝ)|) :
-- imply
  epsilon ≤ (q : ℝ) * |(u : ℝ) * kappa - (v : ℝ) + mu| := by
-- proof
  apply MetaMathlibExt.nearestInteger_reduction_core q M u kappa mu v hu epsilon heq


-- created on 2026-10-20
