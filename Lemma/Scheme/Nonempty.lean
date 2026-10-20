import Mathlib
import sympy.Basic
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_of_bijective_app_of_le_opensRange](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_of_bijective_app_of_le_opensRange.lean)
-/
@[path]
private lemma main
  {X Y : (Scheme : Type (u + 1))} (f : Y ⟶ X) [IsOpenImmersion f] (M : Y.Modules) (L : X.Modules)
  (π : L ⟶ (Scheme.Modules.pushforward f).obj M)
  (hπ : ∀ U : X.Opens, U ≤ f.opensRange → Function.Bijective (π.app U)) :
  Nonempty ((Scheme.Modules.pullback f).obj L ≅ M) := by
  have happ : ∀ U : Y.Opens, ((restrictFunctor f).map π).app U = π.app (f ''ᵁ U) := fun U => rfl
  let _ : IsIso ((restrictFunctor f).map π) := by
    rw [Hom.isIso_iff_isIso_app]
    intro U
    rw [happ, ConcreteCategory.isIso_iff_bijective]
    apply hπ _ (f.image_le_opensRange U)
  refine ⟨Iso.trans (Iso.trans ((restrictFunctorIsoPullback f).app L).symm (asIso ((restrictFunctor f).map π)))
    ((restrictFunctorAdjCounitIso f).app M)⟩


-- created on 2026-10-20
