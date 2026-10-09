import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

/--
[AlgebraicGeometry_Scheme_exists_opens_extension_of_fromSpecStalk](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_opens_extension_of_fromSpecStalk.lean)
-/
@[path]
private lemma main
  {S G H : Scheme.{u}}
  {sG : G ⟶ S}
  {sH : H ⟶ S} [LocallyOfFiniteType sH]
  {η : G} [G.IsGermInjectiveAt η]
  {w : Spec (G.presheaf.stalk η) ⟶ H}
-- given
  (hw : w ≫ sH = G.fromSpecStalk η ≫ sG) :
-- imply
  ∃ (U : G.Opens) (hη : η ∈ U) (v : (U : Scheme.{u}) ⟶ H),
      v ≫ sH = U.ι ≫ sG ∧ U.fromSpecStalkOfMem η hη ≫ v = w := by
-- proof
  obtain ⟨U, hη, v, h1, h2⟩ := spread_out_of_isGermInjective' sG sH w hw
  exact ⟨U, hη, v, h2, h1.symm⟩


-- created on 2026-10-05
