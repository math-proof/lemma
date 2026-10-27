import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.TwistingSheaves
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry


/--
[twistingSheaf_eq_tildeProj_shift](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TwistingSheaves.lean)
-/
@[path]
lemma twistingSheaf_eq_tildeProj_shift
  {A : Type u}
  [CommRing A]
  {σ : Type u}
  [SetLike σ A]
  {d : ℤ} :
-- imply
  twistingSheaf 𝒜 d = tildeProj 𝒜 (GrMod.shift 𝒜 d) :=
-- proof
  rfl

/--
[cor18_coherent_quotient_of_twistingSheaf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TwistingSheaves.lean)
-/
@[path]
lemma cor18_coherent_quotient_of_twistingSheaf
  {A : Type u}
  [CommRing A]
  {σ : Type u}
  [SetLike σ A]
  {ℱ : (Proj 𝒜).Modules}
-- given
  (hcoh : IsCoherentSheaf ℱ) :
-- imply
  ∃ (d : ℕ) (k : ℕ), ∃ (φ : tildeProj 𝒜 ((GrMod.shift 𝒜 (-↑d)).directSumCopies k) ⟶ ℱ), Epi φ :=
-- proof
  coherent_sheaf_quotient_of_twisted_structure_sheaf 𝒜 ℱ hcoh


-- created on 2026-10-23
