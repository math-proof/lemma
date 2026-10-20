import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_Scheme_singleton_sigma_mem_fppfPrecoverage](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_singleton_sigma_mem_fppfPrecoverage.lean)
-/
@[path]
private lemma main
  {R : (CommRingCat : Type (u + 1))} {ι : Type u} [Finite ι] (A : ι → (CommRingCat : Type (u + 1))) (φ : ∀ i, R ⟶ A i)
  (h : Presieve.ofArrows (fun i => Spec (A i)) (fun i => Spec.map (φ i)) ∈ Scheme.fppfPrecoverage (Spec R)) :
  -- imply
  Presieve.singleton (Spec.map (CommRingCat.ofHom (RingHom.pi fun i => (φ i).hom))) ∈ Scheme.fppfPrecoverage (Spec R) := by
  -- proof
  classical
  change Presieve.ofArrows _ _ ∈ Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation) (Spec R) at h
  rw [Scheme.ofArrows_mem_precoverage_iff] at h
  obtain ⟨hsurj, hP⟩ := h
  set F : Spec (CommRingCat.of (Π i, A i)) ⟶ Spec R :=
    Spec.map (CommRingCat.ofHom (RingHom.pi fun i => (φ i).hom)) with hF
  have hcomp : sigmaSpec A ≫ F = Sigma.desc (fun i => Spec.map (φ i)) := by
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [ι_sigmaSpec_assoc, Sigma.ι_comp_desc, hF, ← Spec.map_comp]
    rfl
  change Presieve.singleton F ∈ Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation) (Spec R)
  rw [Scheme.singleton_mem_precoverage_iff]
  refine ⟨fun s => ?_, ?_, ?_⟩
  ·
    obtain ⟨i, y, rfl⟩ := hsurj s
    refine ⟨(Sigma.ι (fun i => Spec (A i)) i ≫ sigmaSpec A).base y, ?_⟩
    change ((Sigma.ι (fun i => Spec (A i)) i ≫ sigmaSpec A) ≫ F).base y = _
    rw [Category.assoc, hcomp, Sigma.ι_comp_desc]
  ·
    have : Flat (Sigma.desc fun i => Spec.map (φ i)) := IsZariskiLocalAtSource.sigmaDesc fun i => (hP i).1
    rw [← hcomp] at this
    apply (MorphismProperty.cancel_left_of_respectsIso @Flat (sigmaSpec A) F).mp this
  ·
    have : LocallyOfFinitePresentation (Sigma.desc fun i => Spec.map (φ i)) :=
      IsZariskiLocalAtSource.sigmaDesc fun i => (hP i).2
    rw [← hcomp] at this
    apply (MorphismProperty.cancel_left_of_respectsIso @LocallyOfFinitePresentation (sigmaSpec A) F).mp this


-- created on 2026-10-20
