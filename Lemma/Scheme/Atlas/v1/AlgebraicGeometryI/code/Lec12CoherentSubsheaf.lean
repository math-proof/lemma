import Mathlib
import sympy.Basic


/--
[submodule_fg_of_noetherian_fg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec12CoherentSubsheaf.lean)
-/
@[path]
lemma submodule_fg_of_noetherian_fg
  {R : Type*}
  [CommRing R]
  [IsNoetherianRing R]
  {M : Type*}
  [AddCommGroup M]
  [Module R M]
  [Module.Finite R M]
  {N : Submodule R M} :
-- imply
  N.FG :=
-- proof
  IsNoetherian.noetherian N

/--
[subsheaf_coherent_of_noetherian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec12CoherentSubsheaf.lean)
-/
@[path]
lemma subsheaf_coherent_of_noetherian
  {R : Type*}
  [CommRing R]
  [IsNoetherianRing R]
  {M : Type*}
  [AddCommGroup M]
  [Module R M]
  {N : Submodule R M}
-- given
  (hM : Module.FinitePresentation R M) :
-- imply
  Module.FinitePresentation R N := by
-- proof
  have hfin : Module.Finite R M := (Module.finitePresentation_iff_finite R M).mp hM
  have hNfg : N.FG := submodule_fg_of_noetherian_fg R M N
  exact (Module.finitePresentation_iff_finite R N).mpr ⟨(Submodule.fg_top _).mpr hNfg⟩


-- created on 2026-10-23
