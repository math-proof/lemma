import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_flat_of_isPullback_of_flat_of_surjective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_flat_of_isPullback_of_flat_of_surjective.lean)
-/
@[path]
private lemma main
  {X Y Y' X' : (Scheme : Type (u + 1))} (ψ : X ⟶ Y) (g : Y' ⟶ Y) [Flat g] [Surjective g] [LocallyOfFinitePresentation g]
  (ψ' : X' ⟶ Y') (π : X' ⟶ X) (h : IsPullback π ψ' ψ g) [Flat ψ'] :
  -- imply
  Flat ψ := by
  -- proof
  have hcod : RingHom.CodescendsAlong RingHom.Flat RingHom.FaithfullyFlat := by
    apply RingHom.CodescendsAlong.mk _ RingHom.Flat.respectsIso
    introv h H
    rw [RingHom.faithfullyFlat_algebraMap_iff] at h
    rw [RingHom.flat_algebraMap_iff] at H ⊢
    apply Module.Flat.of_flat_tensorProduct R T S
  let _ : MorphismProperty.DescendsAlong (@Flat : MorphismProperty (Scheme : Type (u + 1))) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    HasRingHomProperty.descendsAlong_flat hcod
  let _ : MorphismProperty.DescendsAlong (@Flat : MorphismProperty (Scheme : Type (u + 1)))
    (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
    inferInstance
  apply MorphismProperty.of_isPullback_of_descendsAlong (P := @Flat)
    (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) h.flip
    ⟨⟨‹Surjective g›, ‹Flat g›⟩, ‹LocallyOfFinitePresentation g›⟩ ‹Flat ψ'›


-- created on 2026-10-20
