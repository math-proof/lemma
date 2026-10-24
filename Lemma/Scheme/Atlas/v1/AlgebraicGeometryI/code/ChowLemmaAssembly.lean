import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.ChowLemmaAssembly
open AlgebraicGeometry CategoryTheory Limits ChowLemma


namespace ChowLemma

/--
[chow_lemma](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChowLemmaAssembly.lean)
-/
@[path]
lemma chow_lemma
  {X : Scheme.{u}}
  [IsProper X]
  [AlgebraicGeometry.IsIntegral X] :
-- imply
  ∃ (X' : Scheme.{u}), IsProjective X' ∧ Birational X' X := by
-- proof
  obtain ⟨S, f, hf⟩ := IsProper.exists_proper_morphism (X := X)
  haveI : AlgebraicGeometry.IsProper f := hf
  obtain ⟨X', hproj, hbir⟩ :=
    ChowHelperBlowupProjective.chow_helper_blowup_projective f
  exact ⟨X', hproj, ChowHelperBlowupProjective.isBirational_symm hbir⟩

end ChowLemma


-- created on 2026-10-23
