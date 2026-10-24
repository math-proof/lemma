import Lemma.Definitions.Def_CohCarrier_Inst
import Lemma.Definitions.Def_IharaLemma_IdempotentSplitting
import Lemma.Definitions.Def_CuspForm_CornerPairingFamily
import Lemma.Definitions.Def_CuspForm_HeckeLocal
import Lemma.Definitions.Def_GaloisRep_LocalConditions
import Lemma.Definitions.Def_GaloisRep_Residual
import Lemma.Definitions.Def_GaloisRep_Adic

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace CuspForm.heckeLocal

open CohCarrier IharaLemma
open scoped IsMulCommutative

def IsCornerRealization
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (p : ℕ) (ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪))
    (N L : ℕ) [NeZero N] [NeZero L] (S : Set ℕ)
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪)
    (M : Type) [AddCommGroup M] [Module (CuspForm.heckeLocal N S 𝒪 θ) M] [Module 𝒪 M]
    (B : M →ₗ[𝒪] M →ₗ[𝒪] 𝒪) : Prop :=
  ∃ (hcomm : ∀ g h : Gen L S,
        opFamily L ⊤ S 𝒪 g * opFamily L ⊤ S 𝒪 h = opFamily L ⊤ S 𝒪 h * opFamily L ⊤ S 𝒪 g)
    (θbar : Gen L S → IsLocalRing.ResidueField 𝒪)
    (Sp : IdempotentSplitting
      ↥(hdata L ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n)
    (πk : Sp.CornerRing i₀ →ₐ[𝒪] IsLocalRing.ResidueField 𝒪)
    (hpar : ∀ v : H1 L ⊤ 𝒪, v ∈ cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp.e i₀) →
      v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH L ⊤) 𝒪)
    (e : M ≃ₗ[𝒪] ↥(cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp.e i₀))),

    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ L) (hℓN : ¬ ℓ ∣ N),
      θbar (Gen.T ℓ hℓ hℓS hℓL) = θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) ∧
    (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), q ^ 2 ∣ L → θbar (Gen.U q hq hqL) = 0) ∧
    (∀ (hp : p.Prime) (hpL : p ∣ L), (GaloisRepAdic.ofResidualGaloisRep ρbar).IsOrdinaryAt p →
      θbar (Gen.U p hp hpL) ≠ 0) ∧

    (∀ g : Gen L S, πk (Sp.toCornerRing i₀
      ⟨(hdata L ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).op g,
        Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g) ∧

    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓN : ¬ ℓ ∣ N) (m : M),
      ((e (CuspForm.heckeLocal.π N S 𝒪 θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) • m) :
          ↥(cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp.e i₀))) : H1 L ⊤ 𝒪) =
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
          heckeT L ⊤ ℓ 𝒪 ((e m : ↥(cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp.e i₀))) : H1 L ⊤ 𝒪))) ∧

    (∀ m m' : M, B m m' =
      CuspForm.Bfam₀ 𝒪 L ⟨(e m : H1 L ⊤ 𝒪), hpar _ (e m).2⟩ ⟨(e m' : H1 L ⊤ 𝒪), hpar _ (e m').2⟩)

end CuspForm.heckeLocal
