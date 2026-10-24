import Mathlib
import sympy.Basic
import sympy.matrices.inner_product_space.Kirszbraun

/--
[Kirszbraun](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/Kirszbraun.lean)
-/
@[path]
private lemma kirszbraun_general_eq
-- given
  {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {s : Set E} {K : NNReal} {f : E → F}
  (hf : LipschitzOnWith K f s) :
-- imply
  ∃ g : E → F, LipschitzWith K g ∧ Set.EqOn f g s := by
-- proof
  apply InnerProductSpace.KirszbraunWanted.kirszbraun_general hf

/--
[Kirszbraun](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/Kirszbraun.lean)
-/
@[path]
private lemma kirszbraun_eq
-- given
  {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {s : Set E} {K : NNReal} {f : E → F}
  (hf : LipschitzOnWith K f s) :
-- imply
  ∃ g : E → F, LipschitzWith K g ∧ Set.EqOn f g s := by
-- proof
  apply InnerProductSpace.KirszbraunWanted.kirszbraun hf

-- created on 2026-10-10
