import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
[AlgebraicGeometry_exists_isClosedImmersion_iff_comp_eq_of_isSeparated](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_isClosedImmersion_iff_comp_eq_of_isSeparated.lean)
-/
@[path]
private lemma main
  {H S T : Scheme.{u}}
  {q : H ⟶ S} [IsSeparated q]
  {t : T ⟶ S}
  {u v : T ⟶ H}
-- given
  (hu : u ≫ q = t)
  (hv : v ≫ q = t) :
-- imply
  ∃ (Z : Scheme.{u}) (j : Z ⟶ T), IsClosedImmersion j ∧
      ∀ {T' : Scheme.{u}} (ψ : T' ⟶ T), ψ ≫ u = ψ ≫ v ↔ ∃ ψ' : T' ⟶ Z, ψ' ≫ j = ψ := by
-- proof
  refine ⟨pullback (pullback.lift u v (hu.trans hv.symm)) (pullback.diagonal q),
    pullback.fst (pullback.lift u v (hu.trans hv.symm)) (pullback.diagonal q), inferInstance, fun ψ => ⟨fun h => ?_, fun ⟨ψ', hψ'⟩ => ?_⟩⟩
  · refine ⟨pullback.lift ψ (ψ ≫ u) ?_, pullback.lift_fst _ _ _⟩
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.diagonal_snd, Category.comp_id, h]
  · have hc := pullback.condition (f := pullback.lift u v (hu.trans hv.symm)) (g := pullback.diagonal q)
    have h1 := congrArg (fun φ => φ ≫ pullback.fst q q) hc
    have h2 := congrArg (fun φ => φ ≫ pullback.snd q q) hc
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst, pullback.diagonal_snd,
      Category.comp_id] at h1 h2
    rw [← hψ', Category.assoc, Category.assoc, h1, h2]


-- created on 2026-10-05
