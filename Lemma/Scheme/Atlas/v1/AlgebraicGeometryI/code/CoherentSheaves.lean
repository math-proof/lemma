import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.CoherentSheaves
open CoherentSheaves
open CategoryTheory Limits AlgebraicGeometry


namespace CoherentSheaves

/--
[noetherian_coherent_iff_fp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoherentSheaves.lean)
-/
@[path]
lemma noetherian_coherent_iff_fp
  {R : Type*}
  [CommRing R]
  [IsNoetherianRing R]
  {M : Type*}
  [AddCommGroup M]
  [Module R M] :
-- imply
  IsCoherentModule R M ↔ Module.FinitePresentation R M :=
-- proof
  (Module.finitePresentation_iff_finite R M).symm
universe u

end CoherentSheaves

namespace CoherentSheaves

/--
[lemma23_coherent_iff_fg_affine](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoherentSheaves.lean)
-/
@[path]
lemma lemma23_coherent_iff_fg_affine
  {R : Type*}
  [CommRing R]
  {M : Type*}
  [AddCommGroup M]
  [Module R M] :
-- imply
  CoherentSpecFinitelyGenerated.IsLocallyFinitelyGenerated R M ↔ Module.Finite R M :=
-- proof
  CoherentSpecFinitelyGenerated.lemma23_coherent_tilde_iff_fg R M

end CoherentSheaves

namespace CoherentSheaves

/--
[extension_of_sections](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoherentSheaves.lean)
-/
@[path]
lemma extension_of_sections
  [CommRing R]
  {f : R}
  [AddCommGroup M]
  [Module R M]
  {σ : LocalizedModule (Submonoid.powers f) M} :
-- imply
  ∃ (m : M) (s : Submonoid.powers f), σ = LocalizedModule.mk m s :=
-- proof
  LocalizedModule.induction_on (fun m s => ⟨m, s, rfl⟩) σ

end CoherentSheaves


-- created on 2026-10-23
