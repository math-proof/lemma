import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.SpecialFunctions.DickmanDeBruijnExistsUnique
open Real


/--
[existsUnique_isDickmanDeBruijn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/DickmanDeBruijnExistsUnique.lean)
-/
@[path]
private lemma existsUnique_isDickmanDeBruijn_eq
  :
-- imply
  ∃! ρ : ℝ → ℝ, IsDickmanDeBruijn ρ := by
-- proof
  apply Real.existsUnique_isDickmanDeBruijn


-- created on 2026-10-20
