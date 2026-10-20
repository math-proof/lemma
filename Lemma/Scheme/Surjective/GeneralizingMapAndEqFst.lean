import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_surjective_and_generalizingMap_pullback_fst_of_flat](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_surjective_and_generalizingMap_pullback_fst_of_flat.lean)
-/
@[path]
private lemma main
  {X S S' : (Scheme : Type (u + 1))} (f : X ⟶ S) (g : S' ⟶ S) [Flat g] [Surjective g] :
  Surjective (pullback.fst f g) ∧ GeneralizingMap (pullback.fst f g).base ∧ ∀ η : ↥(pullback f g), (∀ η' : ↥(pullback f g), η' ⤳ η → η' = η) → ∀ y : ↥X, y ⤳ (pullback.fst f g).base η → y = (pullback.fst f g).base η := by
  have hs : Surjective (pullback.fst f g) := MorphismProperty.pullback_fst _ _ inferInstance
  have hf : Flat (pullback.fst f g) := MorphismProperty.pullback_fst _ _ inferInstance
  have hg : GeneralizingMap (pullback.fst f g).base := Flat.generalizingMap _
  refine ⟨hs, hg, fun η hη y hy => ?_⟩
  obtain ⟨η', hη', rfl⟩ := hg hy
  rw [hη η' hη']


-- created on 2026-10-20
