import Mathlib
import Structure.Dieudonne_DatumAndHonda
import Instance.Dieudonne_WittVectorHom
import Instance.Dieudonne_WittHomColimit
import Instance.PDivisibleGroup_Basic
import Class.MvFormalGroup_BasicV2
import Instance.MvFormalGroup_PointsV2

set_option autoImplicit false

open scoped TensorProduct
open MvPowerSeries

universe u v

namespace Deformation.HondaSystem

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
variable (r : ℕ) (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞))
variable (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]

structure SplitCoordinates (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v)
    (π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v)) where

  d : ℕ

  hc : ℕ
  he : ℕ

  Gc : ℕ → Type v
  Ge : ℕ → Type v
  [instCommRingGc : ∀ v, CommRing (Gc v)]
  [instHopfGc : ∀ v, HopfAlgebra (ZMod p) (Gc v)]
  [instCommRingGe : ∀ v, CommRing (Ge v)]
  [instHopfGe : ∀ v, HopfAlgebra (ZMod p) (Ge v)]
  sc : ∀ v, Gc (v + 1) →ₐc[ZMod p] Gc v
  se : ∀ v, Ge (v + 1) →ₐc[ZMod p] Ge v

  qc : ∀ v, G v →ₐc[ZMod p] Gc v

  πe : ∀ v, G v →ₐc[ZMod p] Ge v

  σ : ∀ v, Ge v →ₐc[ZMod p] G v

  Θ : ∀ v, G v →ₐc[ZMod p] Gc v ⊗[ZMod p] Ge v

  Φ₀ : MvFormalGroup d (ZMod p)
  κ : ∀ v, MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] Gc v

  Et : ℕ → Type u
  [instCommRingEt : ∀ v, CommRing (Et v)]
  [instHopfEt : ∀ v, HopfAlgebra 𝓞 (Et v)]
  st : ∀ v, Et (v + 1) →ₐc[𝓞] Et v
  θe : ∀ v, ZMod p ⊗[𝓞] Et v →ₐc[ZMod p] Ge v

  ĉ : Fin d → ℕ → ∀ v, Et v

  Mc : Submodule 𝓞 (Fin r → 𝓞)
  Met : Submodule 𝓞 (Fin r → 𝓞)
  α : Module.Basis (Fin d) 𝓞 H₁.L
  abar : Fin d → ℕ → MvPowerSeries (Fin d) (ZMod p)
  a : Fin d → ℕ → MvPowerSeries (Fin d) 𝓞

attribute [instance] SplitCoordinates.instCommRingGc SplitCoordinates.instHopfGc
  SplitCoordinates.instCommRingGe SplitCoordinates.instHopfGe
  SplitCoordinates.instCommRingEt SplitCoordinates.instHopfEt

namespace SplitCoordinates

variable {p r H₁ G s π}
variable (𝒮 : SplitCoordinates p r H₁ G s π)

structure Lawful : Prop where

  hc_add_he : 𝒮.hc + 𝒮.he = r
  isLocalRing_Gc : ∀ v, IsLocalRing (𝒮.Gc v)
  isReduced_Ge : ∀ v, IsReduced (𝒮.Ge v)
  isCocomm_Gc : ∀ v, Coalgebra.IsCocomm (ZMod p) (𝒮.Gc v)
  isCocomm_Ge : ∀ v, Coalgebra.IsCocomm (ZMod p) (𝒮.Ge v)
  finite_Gc : ∀ v, Module.Finite (ZMod p) (𝒮.Gc v)
  finite_Ge : ∀ v, Module.Finite (ZMod p) (𝒮.Ge v)
  sc_surjective : ∀ v, Function.Surjective (𝒮.sc v)
  se_surjective : ∀ v, Function.Surjective (𝒮.se v)
  finrank_Gc : ∀ v, Module.finrank (ZMod p) (𝒮.Gc v) = p ^ (v * 𝒮.hc)
  finrank_Ge : ∀ v, Module.finrank (ZMod p) (𝒮.Ge v) = p ^ (v * 𝒮.he)
  ker_sc : ∀ v, RingHom.ker (𝒮.sc v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (𝒮.Gc (v + 1)) (p ^ v)
  ker_se : ∀ v, RingHom.ker (𝒮.se v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (𝒮.Ge (v + 1)) (p ^ v)
  qc_surjective : ∀ v, Function.Surjective (𝒮.qc v)
  πe_surjective : ∀ v, Function.Surjective (𝒮.πe v)
  ker_πe : ∀ v, RingHom.ker (𝒮.πe v : G v →ₐ[ZMod p] 𝒮.Ge v) = nilradical (G v)
  πe_comp_σ : ∀ v, (𝒮.πe v).comp (𝒮.σ v) = BialgHom.id (ZMod p) (𝒮.Ge v)
  ker_qc : ∀ v, RingHom.ker (𝒮.qc v : G v →ₐ[ZMod p] 𝒮.Gc v) =
    Ideal.map (𝒮.σ v : 𝒮.Ge v →ₐ[ZMod p] G v) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) (𝒮.Ge v)))
  Θ_bijective : ∀ v, Function.Bijective (𝒮.Θ v)
  Θ_apply : ∀ v b, 𝒮.Θ v b = Algebra.TensorProduct.map (𝒮.qc v : G v →ₐ[ZMod p] 𝒮.Gc v)
    (𝒮.πe v : G v →ₐ[ZMod p] 𝒮.Ge v) (Coalgebra.comul (R := ZMod p) b)
  qc_comp_s : ∀ v, (𝒮.qc v).comp (s v) = (𝒮.sc v).comp (𝒮.qc (v + 1))
  πe_comp_s : ∀ v, (𝒮.πe v).comp (s v) = (𝒮.se v).comp (𝒮.πe (v + 1))
  s_comp_σ : ∀ v, (s v).comp (𝒮.σ (v + 1)) = (𝒮.σ v).comp (𝒮.se v)

  Θ_comp_s : ∀ v, (𝒮.Θ v).comp (s v) = (Bialgebra.TensorProduct.map (𝒮.sc v) (𝒮.se v)).comp (𝒮.Θ (v + 1))
  formallyUnramified_Ge : ∀ v, Algebra.FormallyUnramified (ZMod p) (𝒮.Ge v)

  isComm_Φ₀ : 𝒮.Φ₀.IsComm
  κ_surjective : ∀ v, Function.Surjective (𝒮.κ v)
  ker_κ : ∀ v, RingHom.ker (𝒮.κ v) = Ideal.span (Set.range (𝒮.Φ₀.nthSeries (p ^ v)))
  sc_comp_κ : ∀ v, (𝒮.sc v : 𝒮.Gc (v + 1) →ₐ[ZMod p] 𝒮.Gc v).comp (𝒮.κ (v + 1)) = 𝒮.κ v
  counit_κ_X : ∀ v i, Coalgebra.counit (R := ZMod p) (𝒮.κ v (X i)) = 0

  κ_X_mem_radical : ∀ v i, 𝒮.κ v (X i) ∈ (Ideal.span {(p : 𝒮.Gc v)}).radical
  κ_eval : ∀ v F, 𝒮.κ v F = MvFormalGroup.adicEval (Ideal.span {(p : 𝒮.Gc v)}) (fun i => 𝒮.κ v (X i)) F
  comul_κ_X : ∀ v i, Coalgebra.comul (R := ZMod p) (𝒮.κ v (X i)) =
    MvFormalGroup.adicEval (Ideal.span {(p : 𝒮.Gc v ⊗[ZMod p] 𝒮.Gc v)})
      (Sum.elim (fun j => 𝒮.κ v (X j) ⊗ₜ[ZMod p] (1 : 𝒮.Gc v)) (fun j => (1 : 𝒮.Gc v) ⊗ₜ[ZMod p] 𝒮.κ v (X j)))
      (𝒮.Φ₀.toPowerSeries i)
  finrank_quot_nthSeries : Module.finrank (ZMod p)
    (MvPowerSeries (Fin 𝒮.d) (ZMod p) ⧸ Ideal.span (Set.range (𝒮.Φ₀.nthSeries p))) = p ^ 𝒮.hc

  d_eq_finrank_cotangent : 𝒮.d = Module.finrank (ZMod p) (PDivisibleGroup.Hopf.augIdeal (ZMod p) (𝒮.Gc 1)).Cotangent
  ker_κ_le_pow : ∀ N : ℕ, ∃ v, RingHom.ker (𝒮.κ v) ≤
    (Ideal.span (Set.range (X : Fin 𝒮.d → MvPowerSeries (Fin 𝒮.d) (ZMod p)))) ^ N
  κ_injective_joint : ∀ F, (∀ v, 𝒮.κ v F = 0) → F = 0
  κ_surjective_joint : ∀ z : ∀ v, 𝒮.Gc v, (∀ v, 𝒮.sc v (z (v + 1)) = z v) → ∃ F, ∀ v, 𝒮.κ v F = z v

  isCocomm_Et : ∀ v, Coalgebra.IsCocomm 𝓞 (𝒮.Et v)
  free_Et : ∀ v, Module.Free 𝓞 (𝒮.Et v)
  finite_Et : ∀ v, Module.Finite 𝓞 (𝒮.Et v)
  formallyEtale_Et : ∀ v, Algebra.FormallyEtale 𝓞 (𝒮.Et v)
  st_surjective : ∀ v, Function.Surjective (𝒮.st v)
  ker_st : ∀ v, RingHom.ker (𝒮.st v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (𝒮.Et (v + 1)) (p ^ v)
  θe_bijective : ∀ v, Function.Bijective (𝒮.θe v)
  θe_comp : ∀ v, (𝒮.θe v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (𝒮.st v)) =
    (𝒮.se v).comp (𝒮.θe (v + 1))

  bijective_comp_mk : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g] [IsAdicComplete (Ideal.span {(p : g)}) g] (v : ℕ),
    Function.Bijective fun f : 𝒮.Et v →ₐ[𝓞] g => (Ideal.Quotient.mkₐ 𝓞 (Ideal.span {(p : g)})).comp f

  st_ĉ : ∀ i k v, 𝒮.st v (𝒮.ĉ i k (v + 1)) = 𝒮.ĉ i k v
  counit_ĉ : ∀ i k v, Coalgebra.counit (R := 𝓞) (𝒮.ĉ i k v) = 0

  realisation_etale : ∀ v i, ∃ (n : ℕ) (u : Deformation.wittHom (ZMod p) p n (𝒮.Ge v)),
    Deformation.DieudonneModule.of (ZMod p) p (𝒮.Ge v) n u =
      Deformation.DieudonneModule.map (ZMod p) p (𝒮.πe v) (π v ((𝒮.α i : H₁.L) : Fin r → 𝓞)) ∧
    (∀ (k : ℕ) (hk : k < n), (u : TruncatedWittVector p n (𝒮.Ge v)).coeff ⟨n - 1 - k, by omega⟩ =
      𝒮.θe v ((1 : ZMod p) ⊗ₜ[𝓞] 𝒮.ĉ i k v)) ∧
    (∀ k, n ≤ k → 𝒮.θe v ((1 : ZMod p) ⊗ₜ[𝓞] 𝒮.ĉ i k v) = 0)

  isCompl : IsCompl 𝒮.Mc 𝒮.Met
  F_mem_Mc : ∀ m ∈ 𝒮.Mc, H₁.F m ∈ 𝒮.Mc
  V_mem_Mc : ∀ m ∈ 𝒮.Mc, H₁.V m ∈ 𝒮.Mc
  F_mem_Met : ∀ m ∈ 𝒮.Met, H₁.F m ∈ 𝒮.Met
  V_mem_Met : ∀ m ∈ 𝒮.Met, H₁.V m ∈ 𝒮.Met

  pow_F_Mc : ∃ N : ℕ, ∀ m ∈ 𝒮.Mc, ∃ y ∈ 𝒮.Mc, (H₁.F ^ N) m = (p : 𝓞) • y

  F_surjOn_Met : ∀ m ∈ 𝒮.Met, ∃ m' ∈ 𝒮.Met, H₁.F m' = m
  Met_le_range_F : 𝒮.Met ≤ LinearMap.range H₁.F

  mem_Met_iff : ∀ m, m ∈ 𝒮.Met ↔ ∀ N : ℕ, ∃ y, (H₁.F ^ N) y = m
  mem_Mc_iff : ∀ m, m ∈ 𝒮.Mc ↔ ∀ k : ℕ, ∃ N : ℕ, ∃ y, (H₁.F ^ N) m = (p : 𝓞) ^ k • y

  free_Mc : Module.Free 𝓞 𝒮.Mc
  free_Met : Module.Free 𝓞 𝒮.Met
  finrank_Mc : Module.finrank 𝓞 𝒮.Mc = 𝒮.hc
  finrank_Met : Module.finrank 𝓞 𝒮.Met = 𝒮.he

  L_inf_Met : H₁.L ⊓ 𝒮.Met = ⊥

  sh1_le_Lc : ∀ x ∈ (H₁.L).map (𝒮.Mc.subtype ∘ₗ Submodule.projectionOnto 𝒮.Mc 𝒮.Met isCompl),
    x ∈ LinearMap.range H₁.F →
      ∃ y ∈ (H₁.L).map (𝒮.Mc.subtype ∘ₗ Submodule.projectionOnto 𝒮.Mc 𝒮.Met isCompl), x = (p : 𝓞) • y
  sh1_ge_Lc : ∀ y ∈ (H₁.L).map (𝒮.Mc.subtype ∘ₗ Submodule.projectionOnto 𝒮.Mc 𝒮.Met isCompl),
    (p : 𝓞) • y ∈ LinearMap.range H₁.F
  sh2_Lc : LinearMap.range H₁.F ⊔ (H₁.L).map (𝒮.Mc.subtype ∘ₗ Submodule.projectionOnto 𝒮.Mc 𝒮.Met isCompl) = ⊤

  map_πe_π_eq_zero : ∀ v, ∀ m ∈ 𝒮.Mc, Deformation.DieudonneModule.map (ZMod p) p (𝒮.πe v) (π v m) = 0
  map_qc_π_eq_zero : ∀ v, ∀ m ∈ 𝒮.Met, Deformation.DieudonneModule.map (ZMod p) p (𝒮.qc v) (π v m) = 0

  a_map : ∀ i k, (𝒮.a i k).map (algebraMap 𝓞 (ZMod p)) = 𝒮.abar i k
  constantCoeff_a : ∀ i k, MvPowerSeries.constantCoeff (𝒮.a i k) = 0
  abar_tendsto : ∀ i N, ∃ k₀, ∀ k, k₀ ≤ k →
    𝒮.abar i k ∈ (Ideal.span (Set.range (X : Fin 𝒮.d → MvPowerSeries (Fin 𝒮.d) (ZMod p)))) ^ N
  realisation_conn : ∀ v i, ∃ (n : ℕ) (u : Deformation.wittHom (ZMod p) p n (𝒮.Gc v)),
    Deformation.DieudonneModule.of (ZMod p) p (𝒮.Gc v) n u =
      Deformation.DieudonneModule.map (ZMod p) p (𝒮.qc v) (π v ((𝒮.α i : H₁.L) : Fin r → 𝓞)) ∧
    (∀ (k : ℕ) (hk : k < n), (u : TruncatedWittVector p n (𝒮.Gc v)).coeff ⟨n - 1 - k, by omega⟩ = 𝒮.κ v (𝒮.abar i k)) ∧
    (∀ k, n ≤ k → 𝒮.κ v (𝒮.abar i k) = 0)

structure NormalForm : Prop where
  linearPart_zero : (MvFormalGroup.linearPart fun i => 𝒮.a i 0).map (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)})) = 1
  linearPart_one : ∀ i j : Fin 𝒮.d, j ≤ i → MvFormalGroup.linearPart (fun i => 𝒮.a i 1) i j ∈ Ideal.span {(p : 𝓞)}

end SplitCoordinates

end Deformation.HondaSystem
