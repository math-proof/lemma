import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_exists_comp_eq_of_forall_algEquiv_comp_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_comp_eq_of_forall_algEquiv_comp_eq.lean)
-/
@[path]
private lemma main
  {K L : Type u} [Field K] [Field L] [Algebra K L]
  (hfix : ∀ x : L, (∀ σ : AlgEquiv K L L, σ x = x) → ∃ a : K, algebraMap K L a = x)
  {Y : (Scheme : Type (u + 1))} (y : Spec (.of L) ⟶ Y)
  (hy : ∀ σ : AlgEquiv K L L, Spec.map (CommRingCat.ofHom (σ : RingHom L L)) ≫ y = y) :
  -- imply
  ∃ y₀ : Spec (.of K) ⟶ Y, Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ y₀ = y := by
  -- proof
  classical
  obtain ⟨⟨x, ψ⟩, rfl⟩ := (Scheme.SpecToEquivOfField L Y).symm.surjective y
  have hψ : ∀ σ : AlgEquiv K L L, ψ ≫ CommRingCat.ofHom (σ : RingHom L L) = ψ := by
    intro σ
    have h : (Scheme.SpecToEquivOfField L Y).symm ⟨x, ψ ≫ CommRingCat.ofHom (σ : RingHom L L)⟩ = (Scheme.SpecToEquivOfField L Y).symm ⟨x, ψ⟩ := by
      change Spec.map (ψ ≫ _) ≫ Y.fromSpecResidueField x = Spec.map ψ ≫ Y.fromSpecResidueField x
      rw [Spec.map_comp, Category.assoc]
      apply hy σ
    refine eq_of_heq (Sigma.mk.inj ((Scheme.SpecToEquivOfField L Y).symm.injective h)).2
  have hfix' : ∀ a, ∃ b : K, algebraMap K L b = ψ.hom a := fun a =>
    hfix _ fun σ => by
      have := congrArg (fun φ : Y.residueField x ⟶ CommRingCat.of L => φ.hom a) (hψ σ)
      simpa using this
  choose q hq using hfix'
  have hinj := (algebraMap K L).injective
  let ψ₀ : Y.residueField x →+* K :=
    { toFun := q
      map_one' := hinj (by rw [hq, map_one, map_one])
      map_mul' := fun a b => hinj (by rw [hq, map_mul, map_mul, hq, hq])
      map_zero' := hinj (by rw [hq, map_zero, map_zero])
      map_add' := fun a b => hinj (by rw [hq, map_add, map_add, hq, hq]) }
  have hψ₀ : CommRingCat.ofHom ψ₀ ≫ CommRingCat.ofHom (algebraMap K L) = ψ := by
    ext a
    simp [ψ₀, hq]
  refine ⟨Spec.map (CommRingCat.ofHom ψ₀) ≫ Y.fromSpecResidueField x, ?_⟩
  change _ = Spec.map ψ ≫ Y.fromSpecResidueField x
  rw [← hψ₀, Spec.map_comp, Category.assoc]


-- created on 2026-10-20
