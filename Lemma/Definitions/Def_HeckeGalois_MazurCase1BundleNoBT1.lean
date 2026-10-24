import Lemma.Definitions.Def_HeckeGalois_MazurCase1Bundle

set_option autoImplicit false

noncomputable section

open Module

namespace ModularCurve

namespace MazurII142

structure OdaDictionaryNoBT1
    (𝕋 : Type*) [CommRing 𝕋] (J : Type*) [AddCommGroup J] [Module 𝕋 J] (𝔪 : Ideal 𝕋)
    (k : Type*) [Field k]
    (Vrep : Type*) [AddCommGroup Vrep] [Module (𝕋 ⧸ 𝔪) Vrep]
    (HDR : Type*) [AddCommGroup HDR] [Module k HDR]
    (MV : Type*) [AddCommGroup MV] [Module k MV]
    (H0Ω : Type*) [AddCommGroup H0Ω] [Module k H0Ω]
    (H1O : Type*) [AddCommGroup H1O] [Module k H1O] : Type _ where

  DHDR : VerFrobPair k HDR

  DMV : VerFrobPair k MV

  hodgeSub : H0Ω ≃ₗ[k] LinearMap.ker DHDR.frob

  hodgeQuot : H1O ≃ₗ[k] (HDR ⧸ LinearMap.range DHDR.ver)

  pi : HDR →ₗ[k] MV

  pi_surjective : Function.Surjective pi

  pi_ver : pi ∘ₗ DHDR.ver = DMV.ver ∘ₗ pi

  pi_frob : pi ∘ₗ DHDR.frob = DMV.frob ∘ₗ pi

  rank_J : Module.finrank (𝕋 ⧸ 𝔪) (Submodule.torsionBySet 𝕋 J 𝔪) = finrank k HDR

  rank_V : Module.finrank (𝕋 ⧸ 𝔪) Vrep = finrank k MV

namespace OdaDictionaryNoBT1

section Derived

variable {𝕋 : Type*} [CommRing 𝕋] {J : Type*} [AddCommGroup J] [Module 𝕋 J] {𝔪 : Ideal 𝕋}
  {k : Type*} [Field k]
  {Vrep : Type*} [AddCommGroup Vrep] [Module (𝕋 ⧸ 𝔪) Vrep]
  {HDR : Type*} [AddCommGroup HDR] [Module k HDR]
  {MV : Type*} [AddCommGroup MV] [Module k MV]
  {H0Ω : Type*} [AddCommGroup H0Ω] [Module k H0Ω]
  {H1O : Type*} [AddCommGroup H1O] [Module k H1O]
  (P : OdaDictionaryNoBT1 𝕋 J 𝔪 k Vrep HDR MV H0Ω H1O)

abbrev kernelPair : VerFrobPair k (LinearMap.ker P.pi) :=
  P.DHDR.kernelPair P.DMV P.pi P.pi_ver P.pi_frob

abbrev FontaineLayer : Prop :=
  Nontrivial (LinearMap.ker P.pi) →
    ∃ (N : Submodule k (LinearMap.ker P.pi)) (hN : P.kernelPair.Stable N)
      (e : ((LinearMap.ker P.pi) ⧸ N) ≃ₗ[k] MV),
      ∀ z, e ((P.kernelPair.quotientPair N hN).ver z) = P.DMV.ver (e z)

end Derived

end OdaDictionaryNoBT1

universe u v

attribute [local instance] Ideal.Quotient.field

structure Case1GeometryNoBT1 (𝕋 : Type u) [CommRing 𝕋] (J : Type v) [AddCommGroup J] [Module 𝕋 J]
    (𝔪 : Ideal 𝕋) [𝔪.IsMaximal] where

  Vrep : Type u
  [hVrepACG : AddCommGroup Vrep]
  [hVrepMod : Module (𝕋 ⧸ 𝔪) Vrep]

  HDR : Type u
  [hHDRACG : AddCommGroup HDR]
  [hHDRMod : Module (𝕋 ⧸ 𝔪) HDR]

  MV : Type u
  [hMVACG : AddCommGroup MV]
  [hMVMod : Module (𝕋 ⧸ 𝔪) MV]

  H0Ω : Type u
  [hH0ACG : AddCommGroup H0Ω]
  [hH0Mod : Module (𝕋 ⧸ 𝔪) H0Ω]

  H1O : Type u
  [hH1ACG : AddCommGroup H1O]
  [hH1Mod : Module (𝕋 ⧸ 𝔪) H1O]

  pkt : OdaDictionaryNoBT1 𝕋 J 𝔪 (𝕋 ⧸ 𝔪) Vrep HDR MV H0Ω H1O
  [hFD : FiniteDimensional (𝕋 ⧸ 𝔪) HDR]

  hsd : pkt.DMV.SelfDual

  hlayer : pkt.FontaineLayer

attribute [instance] Case1GeometryNoBT1.hVrepACG Case1GeometryNoBT1.hVrepMod
  Case1GeometryNoBT1.hHDRACG Case1GeometryNoBT1.hHDRMod Case1GeometryNoBT1.hMVACG Case1GeometryNoBT1.hMVMod
  Case1GeometryNoBT1.hH0ACG Case1GeometryNoBT1.hH0Mod Case1GeometryNoBT1.hH1ACG Case1GeometryNoBT1.hH1Mod
  Case1GeometryNoBT1.hFD

structure Case1BundleNoBT1 (𝕋 : Type u) [CommRing 𝕋] (J : Type v) [AddCommGroup J] [Module 𝕋 J]
    (𝔪 : Ideal 𝕋) [𝔪.IsMaximal] extends Case1GeometryNoBT1 𝕋 J 𝔪 where

  h94 : finrank (𝕋 ⧸ 𝔪) H1O ≤ 1

  hdimV : finrank (𝕋 ⧸ 𝔪) Vrep = 2

end MazurII142

end ModularCurve

end
