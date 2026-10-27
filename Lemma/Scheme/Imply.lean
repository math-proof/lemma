import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_FormallyUnramified_eq_of_comp_eq_of_isLocalRing](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_FormallyUnramified_eq_of_comp_eq_of_isLocalRing.lean)
-/
@[path]
private lemma main
  {X Y : Scheme} (f : X ⟶ Y) [FormallyUnramified f] [LocallyOfFiniteType f]
  {O : Type u} [CommRing O] [IsLocalRing O]
  (a b : Spec (CommRingCat.of O) ⟶ X) (hf : a ≫ f = b ≫ f)
  {T : Scheme} (t : T ⟶ Spec (CommRingCat.of O))
  (ht : IsLocalRing.closedPoint O ∈ Set.range t.base)
  (hab : t ≫ a = t ≫ b) :
-- imply
  a = b := by
-- proof
  set c : Spec (CommRingCat.of O) ⟶ pullback f f := pullback.lift a b hf with hc
  set E := pullback c (pullback.diagonal f)
  have hE : IsOpenImmersion (pullback.fst c (pullback.diagonal f)) := inferInstance
  have htc : t ≫ c = (t ≫ a) ≫ pullback.diagonal f := by
    apply pullback.hom_ext
    · rw [Category.assoc, hc, pullback.lift_fst, Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, hc, pullback.lift_snd, Category.assoc, pullback.diagonal_snd, Category.comp_id, hab]
  have hrange : Set.range (pullback.fst c (pullback.diagonal f)).base = Set.univ := by
    obtain ⟨t₀, ht₀⟩ := ht
    have hmem : IsLocalRing.closedPoint O ∈ Set.range (pullback.fst c (pullback.diagonal f)).base := by
      refine ⟨(pullback.lift t (t ≫ a) htc).base t₀, ?_⟩
      rw [← Scheme.Hom.comp_apply, pullback.lift_fst, ht₀]
    apply Set.eq_univ_of_forall
    intro x
    exact (IsLocalRing.specializes_closedPoint x).mem_open
      (pullback.fst c (pullback.diagonal f)).isOpenEmbedding.isOpen_range hmem
  have hepi : Epi (pullback.fst c (pullback.diagonal f)).base := by
    rw [TopCat.epi_iff_surjective]
    exact Set.range_eq_univ.mp hrange
  have hiso : IsIso (pullback.fst c (pullback.diagonal f)) := IsOpenImmersion.isIso _
  have hfac : c = (inv (pullback.fst c (pullback.diagonal f)) ≫ pullback.snd c (pullback.diagonal f)) ≫
    pullback.diagonal f := by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
  have ha : a = inv (pullback.fst c (pullback.diagonal f)) ≫ pullback.snd c (pullback.diagonal f) := by
    have := congrArg (· ≫ pullback.fst f f) hfac
    simp only [hc, pullback.lift_fst, Category.assoc, pullback.diagonal_fst, Category.comp_id] at this
    exact this
  have hb : b = inv (pullback.fst c (pullback.diagonal f)) ≫ pullback.snd c (pullback.diagonal f) := by
    have := congrArg (· ≫ pullback.snd f f) hfac
    simp only [hc, pullback.lift_snd, Category.assoc, pullback.diagonal_snd, Category.comp_id] at this
    exact this
  rw [ha, hb]


-- created on 2026-10-20
