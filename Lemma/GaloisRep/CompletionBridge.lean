import Mathlib
import Def.FLTPrelim_Ramification
import Instance.GaloisRep_CompletionBridge
import Abbrev.GaloisRep_CompletionBridge

set_option autoImplicit false

open scoped NNReal Pointwise

variable (q : ℕ) [Fact q.Prime]

noncomputable def padicEmbedding : AlgebraicClosure ℚ →ₐ[ℚ] PadicAlgCl q :=
  IsAlgClosed.lift

lemma mem_padicIntegers_iff {x : PadicAlgCl q} : x ∈ padicIntegers q ↔ ‖x‖₊ ≤ 1 := Iff.rfl

noncomputable def padicPlace : ValuationSubring (AlgebraicClosure ℚ) :=
  (padicIntegers q).comap (padicEmbedding q).toRingHom

theorem mem_padicPlace_iff {x : AlgebraicClosure ℚ} :
    x ∈ padicPlace q ↔ ‖padicEmbedding q x‖₊ ≤ 1 := Iff.rfl

section Galois

noncomputable def localGaloisToGlobal :
    (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
  (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := PadicAlgCl q) (AlgebraicClosure ℚ)).comp
    (MonoidHom.mk' (fun τ => τ.restrictScalars ℚ) (fun _ _ => rfl))

theorem padicEmbedding_localGaloisToGlobal (τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)
    (x : AlgebraicClosure ℚ) :
    padicEmbedding q (localGaloisToGlobal q τ x) = τ (padicEmbedding q x) :=
  AlgEquiv.restrictNormal_commutes (τ.restrictScalars ℚ) (AlgebraicClosure ℚ) x

theorem nnnorm_padicAlgCl_algEquiv (τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)
    (y : PadicAlgCl q) : ‖τ y‖₊ = ‖y‖₊ := by
  ext
  exact (spectralNorm_eq_of_equiv τ y).symm

theorem localGaloisToGlobal_mem_decompositionSubgroup
    (τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) :
    localGaloisToGlobal q τ ∈ (padicPlace q).decompositionSubgroup ℚ := by
  rw [MulAction.mem_stabilizer_iff]
  apply SetLike.ext
  intro x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  have hinv : (localGaloisToGlobal q τ)⁻¹ = localGaloisToGlobal q τ⁻¹ := (map_inv _ τ).symm
  rw [AlgEquiv.smul_def, hinv]
  rw [mem_padicPlace_iff, mem_padicPlace_iff, padicEmbedding_localGaloisToGlobal,
    nnnorm_padicAlgCl_algEquiv]

end Galois
