import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[AlgebraicGeometry_mono_of_formallyUnramified_of_forall_comp_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_mono_of_formallyUnramified_of_forall_comp_eq.lean)
-/
@[path]
private lemma main
    (k : Type u) [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (g : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (φ : X ⟶ Y) (hφ : φ ≫ g = f) [FormallyUnramified φ]
    (hinj : ∀ P Q : Spec (CommRingCat.of k) ⟶ X, P ≫ f = 𝟙 _ → Q ≫ f = 𝟙 _ → P ≫ φ = Q ≫ φ → P = Q) :
    Mono φ := by
  have hcomp : LocallyOfFiniteType (φ ≫ g) := by rw [hφ]; infer_instance
  have hlt : LocallyOfFiniteType φ := locallyOfFiniteType_of_comp φ g
  have hΔ : IsOpenImmersion (pullback.diagonal φ) := inferInstance
  let p : pullback φ φ ⟶ Spec (CommRingCat.of k) := pullback.fst φ φ ≫ f
  have hJ : JacobsonSpace ↥(pullback φ φ) := LocallyOfFiniteType.jacobsonSpace p
  have hsurj : Surjective (pullback.diagonal φ) := by
    refine ⟨fun z => ?_⟩
    by_contra hz
    have hopen : IsOpen (Set.range (pullback.diagonal φ).base) := (pullback.diagonal φ).isOpenEmbedding.isOpen_range
    obtain ⟨z₀, hz₀C, hz₀cl⟩ := nonempty_inter_closedPoints (Z := (Set.range (pullback.diagonal φ).base)ᶜ)
      ⟨z, by simpa using hz⟩ hopen.isClosed_compl.isLocallyClosed
    rw [mem_closedPoints_iff] at hz₀cl
    let ζ : Spec (CommRingCat.of k) ⟶ pullback φ φ := pointOfClosedPoint p z₀ hz₀cl
    have hζ : ζ ≫ p = 𝟙 _ := pointOfClosedPoint_comp p z₀ hz₀cl
    have h1 : (ζ ≫ pullback.fst φ φ) ≫ f = 𝟙 _ := by rw [Category.assoc]; exact hζ
    have h2 : (ζ ≫ pullback.snd φ φ) ≫ f = 𝟙 _ := by
      rw [Category.assoc, ← hφ, ← Category.assoc (pullback.snd φ φ), ← pullback.condition, Category.assoc, hφ]
      exact hζ
    have h12 : (ζ ≫ pullback.fst φ φ) ≫ φ = (ζ ≫ pullback.snd φ φ) ≫ φ := by
      rw [Category.assoc, Category.assoc, pullback.condition]
    have heq := hinj _ _ h1 h2 h12
    have hfac : ζ = (ζ ≫ pullback.fst φ φ) ≫ pullback.diagonal φ := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
      · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, heq]
    apply hz₀C
    refine ⟨((ζ ≫ pullback.fst φ φ).base (IsLocalRing.closedPoint k)), ?_⟩
    have := pointOfClosedPoint_apply p z₀ hz₀cl (IsLocalRing.closedPoint k)
    rw [← this]
    show ((ζ ≫ pullback.fst φ φ) ≫ pullback.diagonal φ).base (IsLocalRing.closedPoint k) = ζ.base (IsLocalRing.closedPoint k)
    rw [← hfac]
  have : IsIso (pullback.diagonal φ) := (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨hΔ, hsurj⟩
  exact (pullback.isIso_diagonal_iff φ).mp this

-- created on 2026-10-20
