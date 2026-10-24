import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralFinite
open Finset StatMech StatMech.FrontierA


/--
[functionalBKR_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralFinite.lean)
-/
@[path]
private lemma functionalBKR_real_eq
  [Fintype E]
  [DecidableEq E]
  {phi : E → Bool → ℝ}
  {f g : ConfigSpace E → ℝ}
-- given
  (hphi0 : ∀ e b, 0 ≤ phi e b)
  (hphi1 : ∀ e, phi e false + phi e true = 1)
  (hf0 : ∀ omega, 0 ≤ f omega)
  (hg0 : ∀ omega, 0 ≤ g omega) :
-- imply
  productExpectation phi (functionalDisjointMax f g) ≤ productExpectation phi f * productExpectation phi g := by
-- proof
  apply StatMech.FrontierA.functionalBKR_real phi hphi0 hphi1 f g hf0 hg0


-- created on 2026-10-23
