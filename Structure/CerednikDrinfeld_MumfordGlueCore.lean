import Structure.CerednikDrinfeld_FormalUpperHalfPlanePoints
import Instance.CerednikDrinfeld_FormalUpperHalfPlaneChartRings

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree

namespace CerednikDrinfeld
namespace FormalOmega

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure MumfordGlueCore
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] (r : ℕ)
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (N : Subgroup (PGL(2, K₀))) : Type 1 where

  Z : ℕ → Scheme.{0}

  zb : ∀ n : ℕ, Z n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))

  zt : ∀ n : ℕ, Z n ⟶ Z (n + 1)

  zt_isPullback : ∀ n : ℕ, IsPullback (zt n) (zb n) (zb (n + 1))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1)))))))

  zb_flat : ∀ n : ℕ, Flat (zb n)

  zb_isSeparated : ∀ n : ℕ, IsSeparated (zb n)

  ζ : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), Spec (CommRingCat.of ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) ⟶ Z n

  ζ_over : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ),
    ζ h n ≫ zb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) =
      Spec.map (CommRingCat.ofHom (algebraMap 𝒪 ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))))

  ζ_zt : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ),
    ζ h n ≫ zt n = Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 (chartERing 𝒪 π r) π) (Nat.le_succ (n + 1)))))) ≫ ζ h (n + 1)

  ζ_isOpenImmersion : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), IsOpenImmersion (ζ h n)

  ζ_cover : ∀ n : ℕ, ∃ S : Finset (Matrix.GeneralLinearGroup (Fin 2) K₀), ∀ z : Z n, ∃ h ∈ S, z ∈ Set.range (ζ h n).base

  ζ_inv : ∀ (g h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), Matrix.ProjGenLinGroup.mk g ∈ N → ζ (g * h) n = ζ h n

  ι : ∀ n : ℕ, ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) →ₐ[𝒪] (chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)})

  ι_ξ : ∀ n : ℕ, ι n (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r)) = Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r)

  ι_η : ∀ n : ℕ, ι n (Ideal.Quotient.mk _ (chartERing.η 𝒪 π r)) * Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r) =
    algebraMap 𝒪 (chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}) π

  ι_isLocalization : ∀ n : ℕ, @IsLocalization.Away ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) _ (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r)) (chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}) _ (ι n).toRingHom.toAlgebra

  τ : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), (chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}) ≃ₐ[𝒪] (chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)})

  τ_spec : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀), Vertex.act g (stdVertex 𝒪 K₀) = (stdVertex 𝒪 K₀) → ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B]
    (y : (chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}) →ₐ[𝒪] B) (d d' : DeligneDatum (K := K₀) π B),
    (d.line (stdFullLattice K₀) =
          Submodule.span B {(y (Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(y (Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 +
              (algebraMap 𝒪 B π) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
    (d'.line (stdFullLattice K₀) =
          Submodule.span B {((y.comp (τ g n).toAlgHom) (Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d'.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {((y.comp (τ g n).toAlgHom) (Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 +
              (algebraMap 𝒪 B π) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d'.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
    DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ d d'

  α : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) ≃ₐ[𝒪] ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))

  α_spec : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀),
    (Vertex.act g (stdVertex 𝒪 K₀) = (stdVertex 𝒪 K₀) ∧ Vertex.act g (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (Vertex.act g₁ (stdVertex 𝒪 K₀))) ∨ (Vertex.act g (stdVertex 𝒪 K₀) = (Vertex.act g₁ (stdVertex 𝒪 K₀)) ∧ Vertex.act g (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (stdVertex 𝒪 K₀)) →
    ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B]
    (xq : ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) →ₐ[𝒪] B) (d d' : DeligneDatum (K := K₀) π B),
    (d.line (stdFullLattice K₀) =
          Submodule.span B {((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
            (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
    (d'.line (stdFullLattice K₀) =
          Submodule.span B {(((xq.comp (α g n).toAlgHom).comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d'.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (((xq.comp (α g n).toAlgHom).comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
            (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d'.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
    DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ d d'

  ζ_edge : ∀ (h g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ),
    (Vertex.act g (stdVertex 𝒪 K₀) = (stdVertex 𝒪 K₀) ∧ Vertex.act g (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (Vertex.act g₁ (stdVertex 𝒪 K₀))) ∨ (Vertex.act g (stdVertex 𝒪 K₀) = (Vertex.act g₁ (stdVertex 𝒪 K₀)) ∧ Vertex.act g (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (stdVertex 𝒪 K₀)) →
    ζ (h * g) n = Spec.map (CommRingCat.ofHom (α g n).toAlgHom.toRingHom) ≫ ζ h n

  ζ_vertex : ∀ (h g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), Vertex.act g (stdVertex 𝒪 K₀) = (stdVertex 𝒪 K₀) →
    Spec.map (CommRingCat.ofHom (ι n).toRingHom) ≫ ζ (h * g) n =
      Spec.map (CommRingCat.ofHom (τ g n).toAlgHom.toRingHom) ≫ Spec.map (CommRingCat.ofHom (ι n).toRingHom) ≫ ζ h n

  ζ_preimage_le : ∀ (h h' : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ),
    (∀ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N →
      ¬ ((Vertex.act h' (stdVertex 𝒪 K₀) = Vertex.act (g * h) (stdVertex 𝒪 K₀) ∧ Vertex.act h' (Vertex.act g₁ (stdVertex 𝒪 K₀)) = Vertex.act (g * h) (Vertex.act g₁ (stdVertex 𝒪 K₀))) ∨
         (Vertex.act h' (stdVertex 𝒪 K₀) = Vertex.act (g * h) (Vertex.act g₁ (stdVertex 𝒪 K₀)) ∧ Vertex.act h' (Vertex.act g₁ (stdVertex 𝒪 K₀)) = Vertex.act (g * h) (stdVertex 𝒪 K₀)))) →
    (ζ h' n) ⁻¹ᵁ (@Scheme.Hom.opensRange _ _ (ζ h n) (ζ_isOpenImmersion h n)) ≤
      (⨆ (_ : ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧
          (Vertex.act h' (stdVertex 𝒪 K₀) = Vertex.act (g * h) (stdVertex 𝒪 K₀) ∨ Vertex.act h' (stdVertex 𝒪 K₀) = Vertex.act (g * h) (Vertex.act g₁ (stdVertex 𝒪 K₀)))),
        PrimeSpectrum.basicOpen (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) (chartERing.ξ 𝒪 π r))) ⊔
      (⨆ (_ : ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧
          (Vertex.act h' (Vertex.act g₁ (stdVertex 𝒪 K₀)) = Vertex.act (g * h) (stdVertex 𝒪 K₀) ∨ Vertex.act h' (Vertex.act g₁ (stdVertex 𝒪 K₀)) = Vertex.act (g * h) (Vertex.act g₁ (stdVertex 𝒪 K₀)))),
        PrimeSpectrum.basicOpen (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) (chartERing.η 𝒪 π r)))

  desc : ∀ (n : ℕ) (T : Scheme.{0}) (t : Matrix.GeneralLinearGroup (Fin 2) K₀ → (Spec (CommRingCat.of ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) ⟶ T)),
    (∀ g h : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N → t (g * h) = t h) →
    (∀ h g : Matrix.GeneralLinearGroup (Fin 2) K₀,
      (Vertex.act g (stdVertex 𝒪 K₀) = (stdVertex 𝒪 K₀) ∧ Vertex.act g (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (Vertex.act g₁ (stdVertex 𝒪 K₀))) ∨ (Vertex.act g (stdVertex 𝒪 K₀) = (Vertex.act g₁ (stdVertex 𝒪 K₀)) ∧ Vertex.act g (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (stdVertex 𝒪 K₀)) →
      t (h * g) = Spec.map (CommRingCat.ofHom (α g n).toAlgHom.toRingHom) ≫ t h) →
    (∀ h g : Matrix.GeneralLinearGroup (Fin 2) K₀, Vertex.act g (stdVertex 𝒪 K₀) = (stdVertex 𝒪 K₀) →
      Spec.map (CommRingCat.ofHom (ι n).toRingHom) ≫ t (h * g) =
        Spec.map (CommRingCat.ofHom (τ g n).toAlgHom.toRingHom) ≫ Spec.map (CommRingCat.ofHom (ι n).toRingHom) ≫ t h) →
    ∃! u : Z n ⟶ T, ∀ h : Matrix.GeneralLinearGroup (Fin 2) K₀, ζ h n ≫ u = t h

end FormalOmega
end CerednikDrinfeld
