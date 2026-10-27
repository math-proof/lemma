import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[AlgebraicGeometry_IsFinite_of_comp_of_surjective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsFinite_of_comp_of_surjective.lean)
-/
@[path]
private lemma main
  {X Y Z : Scheme} {f : X ⟶ Y} {g : Y ⟶ Z}
-- given
  [Surjective f] [IsFinite (f ≫ g)] [LocallyOfFiniteType g] [IsSeparated g] :
-- imply
  IsFinite g := by
-- proof
  let _ : UniversallyClosed g := UniversallyClosed.of_comp_surjective f g
  let _ : IsProper g := IsProper.mk
  let _ : LocallyQuasiFinite g := by
    rw [locallyQuasiFinite_iff_finite_preimage_singleton]
    intro z
    have hfin := (f ≫ g).finite_preimage_singleton z
    have hsub : g.base ⁻¹' {z} ⊆ f.base '' ((f ≫ g).base ⁻¹' {z}) := by
      intro y hy
      obtain ⟨x, rfl⟩ := f.surjective y
      exact ⟨x, by simpa [Scheme.Hom.comp_apply] using hy, rfl⟩
    refine (hfin.image _).subset hsub
  apply IsFinite.of_isProper_of_locallyQuasiFinite g


-- created on 2026-10-20
