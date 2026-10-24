import Mathlib
import sympy.Basic
open IntermediateField


namespace Polynomial

/--
[exists_pos_adjoinRoot_algEquiv_of_l1Norm_sub_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Normed/Field/AdjoinRootStability.lean)
-/
@[path]
lemma exists_pos_adjoinRoot_algEquiv_of_l1Norm_sub_lt
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
  obtain ⟨δroot, hδroot, hroot⟩ :=
    exists_isClosestConjugate_root_of_l1Norm_sub_lt K f hf hirr hsep
  obtain ⟨δirr, hδirr, hirrsep⟩ :=
    exists_pos_irreducible_and_separable_of_l1Norm_sub_lt K f hf hirr hsep
  refine
    ⟨min δroot δirr, lt_min hδroot hδirr,
      fun g hg hclose => ?_⟩
  have hcloseRoot :
    l1Norm (NormedField.toAbsoluteValue K) (f - g) < δroot :=
    hclose.trans_le (min_le_left _ _)
  have hcloseIrr :
    l1Norm (NormedField.toAbsoluteValue K) (f - g) < δirr :=
    hclose.trans_le (min_le_right _ _)
  obtain ⟨hgirr, _⟩ := hirrsep g hg hcloseIrr
  obtain ⟨β, hβ⟩ :=
    IsAlgClosed.exists_aeval_eq_zero
      (AlgebraicClosure K) g (degree_pos_of_irreducible hgirr).ne'
  obtain ⟨α, hα, _, hadjoin⟩ :=
    hroot g hg hcloseRoot β hβ
  have hαint : IsIntegral K α :=
    (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  have hβint : IsIntegral K β :=
    (Algebra.IsAlgebraic.isAlgebraic β).isIntegral
  have hminα : f = minpoly K α :=
    minpoly.eq_of_irreducible_of_monic hirr hα hf
  have hminβ : g = minpoly K β :=
    minpoly.eq_of_irreducible_of_monic hgirr hβ hg
  have eα :
    AdjoinRoot f ≃ₐ[K] IntermediateField.adjoin K {α} := by
    rw [hminα]
    exact IntermediateField.adjoinRootEquivAdjoin K hαint
  have eβ :
    AdjoinRoot g ≃ₐ[K] IntermediateField.adjoin K {β} := by
    rw [hminβ]
    exact IntermediateField.adjoinRootEquivAdjoin K hβint
  exact
    ⟨eα.trans ((IntermediateField.equivOfEq hadjoin).trans eβ.symm)⟩

end Polynomial


-- created on 2026-10-20
-- updated on 2026-10-23
