import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_locallyOfFiniteType_and_quasiCompact_of_finite_openCover](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_locallyOfFiniteType_and_quasiCompact_of_finite_openCover.lean)
-/
@[path]
private lemma main
  {K : Type u} {X J : (Scheme : Type (u + 1))} [CommRing K]
  {f : X ⟶ Spec (CommRingCat.of K)} [LocallyOfFiniteType f] [QuasiCompact f]
  {σ : J ⟶ Spec (CommRingCat.of K)}
  {n : ℕ} (cov : Fin n → (X ⟶ J)) (hoi : ∀ i, IsOpenImmersion (cov i))
  (cov_over : ∀ i, cov i ≫ σ = f) (hcov : ⋃ i, Set.range (cov i).base = Set.univ) :
  -- imply
  LocallyOfFiniteType σ ∧ QuasiCompact σ := by
  -- proof
  constructor
  ·
    have hmem : ∀ x, ∃ i, x ∈ Set.range (cov i).base := by
      intro x
      have hx : x ∈ ⋃ i, Set.range (cov i).base := hcov ▸ Set.mem_univ x
      simpa [Set.mem_iUnion, Set.mem_range] using hx
    have hloc : ∀ i, LocallyOfFiniteType (cov i ≫ σ) := by
      intro i
      rw [cov_over i]
      infer_instance
    let 𝒰 : J.OpenCover := Scheme.Cover.mkOfCovers (Fin n) (fun _ => X) cov hmem (fun j => hoi j)
    apply IsZariskiLocalAtSource.of_openCover 𝒰 hloc
  ·
    have hX : CompactSpace X :=
      HasAffineProperty.iff_of_isAffine (P := @QuasiCompact).mp ‹QuasiCompact f›
    have hJ : CompactSpace J := by
      constructor
      rw [← hcov]
      refine isCompact_iUnion (fun i => ?_)
      rw [← Set.image_univ]
      apply (CompactSpace.isCompact_univ).image (cov i).continuous
    refine HasAffineProperty.iff_of_isAffine (P := @QuasiCompact).mpr hJ


-- created on 2026-10-20
