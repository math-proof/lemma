/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Normed/Field/AdjoinRootStability.lean -/

import sympy.atlas.Analysis.Normed.Field.ContinuityOfRoots
/-! # AdjoinRoot stability under small monic perturbations

Generic prerequisite stage `N234-B6`: a small monic `l1Norm` perturbation of an
irreducible separable polynomial yields a noncanonically `K`-algebra-equivalent
`AdjoinRoot`.

ATLAS source-to-API map:
- [`v1/Atlas/NumberTheoryI/code/KrasnerLemma.lean` lines 540-549](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/KrasnerLemma.lean#L540-L549): the close-root /
  equal-adjoin input (`Theorem_11_19`), formalized here as
  `Polynomial.exists_isClosestConjugate_root_of_l1Norm_sub_lt`.
- [`v1/Atlas/NumberTheoryI/code/KrasnerLemma.lean` lines 551-603](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/KrasnerLemma.lean#L551-L603): perturbation
  irreducibility/separability (`continuity_of_roots_irreducible_separable`),
  formalized here as
  `Polynomial.exists_pos_irreducible_and_separable_of_l1Norm_sub_lt`.
- [`v1/Atlas/NumberTheoryI/code/LocalGlobal.lean` lines 397-416](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean#L397-L416): ATLAS's explicit
  roots-to-`AdjoinRoot` equivalence helper (via `adjoinRootEquivAdjoin` +
  `equivOfEq`).
- [`v1/Atlas/NumberTheoryI/code/LocalGlobal.lean` lines 661-675](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean#L661-L675): the use of the
  equal-adjoin certificate in N234.

This is a generic prerequisite stage only. It claims only a noncanonical
algebra equivalence. It does not claim type equality, splitting-field equality,
a topological/isometric equivalence, dense approximation, a global field, a
place, or a completion equivalence.
-/

namespace Polynomial

open IntermediateField

theorem exists_pos_adjoinRoot_algEquiv_of_l1Norm_sub_lt
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K]
    (f : K[X]) (hf : f.Monic) (hirr : Irreducible f)
    (hsep : f.Separable) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g : K[X], g.Monic →
      l1Norm (NormedField.toAbsoluteValue K) (f - g) < δ →
      Nonempty (AdjoinRoot f ≃ₐ[K] AdjoinRoot g) := by
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
