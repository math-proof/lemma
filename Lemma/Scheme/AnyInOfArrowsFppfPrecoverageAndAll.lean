import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_Scheme_exists_ofArrows_mem_fppfPrecoverage_of_mem_fppfTopology](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_ofArrows_mem_fppfPrecoverage_of_mem_fppfTopology.lean)
-/
@[path]
private lemma main
  {R : (CommRingCat : Type (u + 1))}
  (S : Sieve (Spec R))
  (hS : S ∈ Scheme.fppfTopology (Spec R)) :
  ∃ (ι : Type u) (_ : Finite ι) (A : ι → (CommRingCat : Type (u + 1))) (φ : ∀ i, R ⟶ A i), Presieve.ofArrows (fun i => Spec (A i)) (fun i => Spec.map (φ i)) ∈ Scheme.fppfPrecoverage (Spec R) ∧ ∀ i, S (Spec.map (φ i)) := by
  classical
  let _ : (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty (Scheme : Type (u + 1))).ContainsIdentities :=
    ⟨fun X => ⟨inferInstance, inferInstance⟩⟩
  let _ : (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty (Scheme : Type (u + 1))).RespectsIso :=
    MorphismProperty.RespectsIso.inf _ _
  let _ : Scheme.fppfPrecoverage.HasIsos := by
    dsimp [Scheme.fppfPrecoverage]
    infer_instance
  let _ : Scheme.fppfPrecoverage.HasPullbacks := by
    dsimp [Scheme.fppfPrecoverage]
    infer_instance
  obtain ⟨T, hT, hTS⟩ :=
    (Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition (J := Scheme.fppfPrecoverage)).mp hS
  obtain ⟨E, rfl⟩ := Precoverage.mem_iff_exists_zeroHypercover.mp hT
  have hE : Presieve.ofArrows E.X E.f ∈ Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation) (Spec R) :=
    E.mem₀
  rw [Scheme.ofArrows_mem_precoverage_iff] at hE
  obtain ⟨hsurj, hP⟩ := hE
  have key : ∀ x : Spec R, ∃ (k : E.I₀) (U : (E.X k).affineOpens), x ∈ Set.range (U.1.ι ≫ E.f k).base := by
    intro x
    obtain ⟨k, y, rfl⟩ := hsurj x
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
      (E.X k).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    exact ⟨k, ⟨U, hU⟩, ⟨⟨y, hyU⟩, rfl⟩⟩
  choose k U hxU using key
  have hopen : ∀ x : Spec R, IsOpen (Set.range ((U x).1.ι ≫ E.f (k x)).base) := fun x => by
    let _ : Flat (E.f (k x)) := (hP (k x)).1
    let _ : LocallyOfFinitePresentation (E.f (k x)) := (hP (k x)).2
    apply ((E.f (k x)).isOpenMap.comp (U x).1.ι.isOpenMap).isOpen_range
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : Spec R => Set.range ((U x).1.ι ≫ E.f (k x)).base) hopen
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hxU x⟩)
  let W : {x // x ∈ t} → (Scheme : Type (u + 1)) := fun z => ((U z.1).1 : (Scheme : Type (u + 1)))
  let hWaff : ∀ z, IsAffine (W z) := fun z => (U z.1).2
  let g : ∀ z, W z ⟶ Spec R := fun z => (U z.1).1.ι ≫ E.f (k z.1)
  let A : {x // x ∈ t} → (CommRingCat : Type (u + 1)) := fun z => (W z).presheaf.obj (op ⊤)
  let φ : ∀ z, R ⟶ A z := fun z => Spec.preimage ((W z).isoSpec.inv ≫ g z)
  have hφ : ∀ z, Spec.map (φ z) = (W z).isoSpec.inv ≫ g z := fun z => Spec.map_preimage _
  refine ⟨{x // x ∈ t}, inferInstance, A, φ, ?_, fun z => ?_⟩
  ·
    change Presieve.ofArrows _ _ ∈ Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation) (Spec R)
    rw [Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun z => ?_⟩
    ·
      obtain ⟨x', hx't, hx⟩ : ∃ x' ∈ t, x ∈ Set.range ((U x').1.ι ≫ E.f (k x')).base := by
        simpa only [Set.mem_iUnion, exists_prop] using ht (Set.mem_univ x)
      obtain ⟨y, rfl⟩ := hx
      refine ⟨⟨x', hx't⟩, (W ⟨x', hx't⟩).isoSpec.hom.base y, ?_⟩
      rw [hφ]
      change ((W ⟨x', hx't⟩).isoSpec.hom ≫ (W ⟨x', hx't⟩).isoSpec.inv ≫ g ⟨x', hx't⟩).base y = _
      rw [Iso.hom_inv_id_assoc]
    ·
      rw [hφ]
      let _ : Flat (E.f (k z.1)) := (hP (k z.1)).1
      let _ : LocallyOfFinitePresentation (E.f (k z.1)) := (hP (k z.1)).2
      exact ⟨inferInstance, inferInstance⟩
  ·
    rw [hφ, ← Category.assoc]
    exact S.downward_closed (hTS _ _ (Presieve.ofArrows.mk (k z.1))) _


-- created on 2026-10-20
