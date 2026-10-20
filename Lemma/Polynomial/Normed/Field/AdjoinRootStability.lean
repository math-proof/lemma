import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Normed.Field.AdjoinRootStability
open IntermediateField
open Polynomial


/--
[exists_pos_adjoinRoot_algEquiv_of_l1Norm_sub_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Normed/Field/AdjoinRootStability.lean)
-/
@[path]
private lemma exists_pos_adjoinRoot_algEquiv_of_l1Norm_sub_lt_eq
  [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {f : K[X]}
-- given
  (hf : f.Monic)
  (hirr : Irreducible f)
  (hsep : f.Separable) :
-- imply
  ∃ δ : ℝ, 0 < δ ∧ ∀ g : K[X], g.Monic →
    l1Norm (NormedField.toAbsoluteValue K) (f - g) < δ →
    Nonempty (AdjoinRoot f ≃ₐ[K] AdjoinRoot g) := by
-- proof
  apply Polynomial.exists_pos_adjoinRoot_algEquiv_of_l1Norm_sub_lt K f hf hirr hsep


-- created on 2026-10-20
