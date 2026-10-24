import Lemma.Definitions.Def_CerednikDrinfeld_Ribbon
import Lemma.Definitions.Def_HeckeGalois_EichlerShimura
import Lemma.Definitions.Def_Compat_Mathlib430

set_option autoImplicit false

namespace CerednikDrinfeld

open ModularCurve

structure JPrimeTorsionDatum (p : ℕ) (E V : Type) [Fintype E] [Fintype V] [DecidableEq V]
    (A : ValuationSubring (AlgebraicClosure ℚ)) : Type 1 where

  D : DegeneracyData E V

  H : HeckeData D

  T : Type
  [instAddCommGroup : AddCommGroup T]
  [instFinite : Finite T]

  pTorsion : ∀ t : T, p • t = 0

  hecke : HeckeAlg →+* Module.End ℤ T

  gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* AddAut T

  comm : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : HeckeAlg) (t : T),
    gal σ (hecke x t) = hecke x (gal σ t)

  finiteLevel : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ y ∈ L, σ y = y) → gal σ = 1

  toric : AddSubgroup T

  toricEquiv : ↥toric ≃+ (↥(ribbonKernel D) →ₗ[ℤ] ZMod p)

  sp : ↥(⨅ σ ∈ A.inertiaSubgroupIn ℚ, ((gal σ).toAddMonoidHom - AddMonoidHom.id T).ker) →+
    ribbonComponentGroup D

attribute [instance] JPrimeTorsionDatum.instAddCommGroup JPrimeTorsionDatum.instFinite

namespace JPrimeTorsionDatum

variable {p : ℕ} {E V : Type} [Fintype E] [Fintype V] [DecidableEq V]
  {A : ValuationSubring (AlgebraicClosure ℚ)}

noncomputable def invariants (Dm : JPrimeTorsionDatum p E V A) : AddSubgroup Dm.T :=
  ⨅ σ ∈ A.inertiaSubgroupIn ℚ, ((Dm.gal σ).toAddMonoidHom - AddMonoidHom.id Dm.T).ker

noncomputable def W (Dm : JPrimeTorsionDatum p E V A) (𝔪 : Ideal HeckeAlg) : AddSubgroup Dm.T :=
  ⨅ x ∈ 𝔪, (Dm.hecke x).toAddMonoidHom.ker

end JPrimeTorsionDatum

end CerednikDrinfeld
