import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma of_forall_exists_iso_morphismRestrict_eq_pullback_fst
  (P : MorphismProperty (Scheme : Type (u + 1)))
  [IsZariskiLocalAtTarget P] [P.IsStableUnderBaseChange]
  {S D B G : (Scheme : Type (u + 1))} (g : G ⟶ S) (hg : P g) (b : B ⟶ S) (π : D ⟶ B)
  (hloc : ∀ p : B, ∃ U : B.Opens, p ∈ U ∧ ∃ e : ((TopologicalSpace.Opens.map π.base).obj U : (Scheme : Type (u + 1))) ≅ pullback (U.ι ≫ b) g, e.hom ≫ pullback.fst (U.ι ≫ b) g = morphismRestrict π U) :
  P π := by
  choose U hpU e he using hloc
  have hU : iSup U = ⊤ := top_le_iff.mp fun p _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨p, hpU p⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top U hU fun p => ?_
  rw [← he p, P.cancel_left_of_respectsIso]
  apply P.pullback_fst _ _ hg
/--
[AlgebraicGeometry_flat_and_surjective_of_forall_exists_iso_morphismRestrict_eq_pullback_fst](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_flat_and_surjective_of_forall_exists_iso_morphismRestrict_eq_pullback_fst.lean)
-/
@[path]
private lemma main
  {S D B G : (Scheme : Type (u + 1))} (g : G ⟶ S) [Flat g] [Surjective g] (b : B ⟶ S) (π : D ⟶ B)
  (hloc : ∀ p : B, ∃ U : B.Opens, p ∈ U ∧ ∃ e : ((TopologicalSpace.Opens.map π.base).obj U : (Scheme : Type (u + 1))) ≅ pullback (U.ι ≫ b) g, e.hom ≫ pullback.fst (U.ι ≫ b) g = morphismRestrict π U) :
  -- imply
  Flat π ∧ Surjective π :=
  ⟨of_forall_exists_iso_morphismRestrict_eq_pullback_fst @Flat g ‹_› b π hloc,
    of_forall_exists_iso_morphismRestrict_eq_pullback_fst @Surjective g ‹_› b π hloc⟩


-- created on 2026-10-20
