import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.CoherentSpecFinitelyGenerated
open CoherentSpecFinitelyGenerated


namespace CoherentSpecFinitelyGenerated

/--
[lemma23_coherent_tilde_iff_fg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoherentSpecFinitelyGenerated.lean)
-/
@[path]
lemma lemma23_coherent_tilde_iff_fg
  {R : Type*}
  [CommRing R]
  {M : Type*}
  [AddCommGroup M]
  [Module R M] :
-- imply
  IsLocallyFinitelyGenerated R M ↔ Module.Finite R M := by
-- proof
  constructor
  ·
    rintro ⟨s, hs, hfin⟩
    exact Module.Finite.of_localizationSpan_finite s hs hfin
  ·
    intro hfg
    refine ⟨{1}, by simp, ?_⟩
    intro ⟨r, hr⟩
    simp at hr; subst hr
    exact Module.Finite.of_isLocalizedModule (Submonoid.powers (1 : R))
      (LocalizedModule.mkLinearMap (Submonoid.powers (1 : R)) M)

end CoherentSpecFinitelyGenerated


-- created on 2026-10-23
