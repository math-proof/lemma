import Mathlib
import Structure.CerednikDrinfeld_MumfordTower

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

namespace CerednikDrinfeld
namespace FormalOmega
namespace MumfordTower

structure NrPresentation
    {r : ℕ} (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (N : Subgroup (PGL(2, K₀)))
    (DM : MumfordTower 𝒪 π K₀ r g₁ N)
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (X : ℕ → Scheme.{0}) (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
    (G₂ : Type) [Group G₂] (a : ∀ n : ℕ, G₂ →* Aut (X n))
    (pr₁ : ∀ n : ℕ, X n ⟶ DM.Z n) (pr₂ : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})))
    (E : Subgroup G₂) : Type 1 where

  X' : ℕ → Scheme.{0}

  xb' : ∀ n : ℕ, X' n ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}))

  xt' : ∀ n : ℕ, X' n ⟶ X' (n + 1)

  a' : ∀ n : ℕ, G₂ →* Aut (X' n)

  qX : ∀ n : ℕ, X' n ⟶ X n

  hq : ∀ n : ℕ, IsPullback (qX n) (xb' n) (xb n)
    (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) (algebraMap 𝒪 Onr)
      (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))))

  hcart' : ∀ n : ℕ, IsPullback (xt' n) (xb' n) (xb' (n + 1))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 Onr π) (Nat.le_succ (n + 1)))))))

  hq_xt : ∀ n : ℕ, xt' n ≫ qX (n + 1) = qX n ≫ xt n

  hq_a : ∀ (n : ℕ) (g : G₂), (a' n g).hom ≫ qX n = qX n ≫ (a n g).hom

  ha'_over : ∀ (n : ℕ) (g : G₂), (a' n g).hom ≫ xb' n = xb' n

  κ' : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), Spec (CommRingCat.of ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})) ⟶ X' n

  κ'_pr₁ : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ)
      (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra Onr B] [IsScalarTower 𝒪 Onr B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
      (xbar : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) →ₐ[Onr] B) (d P : DeligneDatum (K := K₀) π B),
      (d.line (stdFullLattice K₀) =
              Submodule.span B {(xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
            d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
              (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
                (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
            d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
      DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d P →
      Spec.map (CommRingCat.ofHom xbar.toRingHom) ≫ κ' h n ≫ qX n ≫ pr₁ n = DM.q n B hB P

  κ'_pr₂ : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ),
      κ' h n ≫ qX n ≫ pr₂ n = Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})
          ((algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r)).comp ((AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val.toRingHom))
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))

  κ'_xb' : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ),
      κ' h n ≫ xb' n = Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})
          (algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r))
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))

  κ'_isOpenImmersion : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), IsOpenImmersion (κ' h n)

  cover : ∀ (n : ℕ) (x : X' n), ∃ (g : G₂) (h : Matrix.GeneralLinearGroup (Fin 2) K₀), x ∈ Set.range (κ' h n ≫ (a' n g).hom).base

  parity : ∀ (n : ℕ) (g : G₂) (h h' : Matrix.GeneralLinearGroup (Fin 2) K₀),
      (Set.range (κ' h n).base ∩ Set.range (κ' h' n ≫ (a' n g).hom).base).Nonempty → g ∈ E

end MumfordTower
end FormalOmega
end CerednikDrinfeld
