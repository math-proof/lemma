import Lemma.Hyperreal.UFn.of.All_Ufn
import sympy.polys.polyroots
open Hyperreal


@[main]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  √x ≥ 0 := by
-- proof
  apply UFn.of.All_Ufn x
  intro x
  apply Filter.Germ.coe_le.mpr ∘ Filter.Eventually.of_forall
  simp [Real.sqrt_nonneg]


-- created on 2025-12-09
