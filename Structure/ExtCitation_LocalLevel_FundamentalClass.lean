import Mathlib
import Instance.ExtCitation_LocalLevelResidues
import Def.GroupCohomology_CyclicCarry

set_option autoImplicit false

open CategoryTheory groupCohomology

namespace ExtCitation.LocalLevel

variable (q : ℕ) [Fact q.Prime]

structure IsBase (L : IntermediateField ℚ_[q] (PadicAlgCl q)) (G : Type) [Group G] [MulSemiringAction G L]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) : Prop where
  le : K ≤ L
  mem_iff : ∀ x : L, (x : PadicAlgCl q) ∈ K ↔ ∀ g : G, g • x = x

structure IsUnramOverlayerDatum (L : IntermediateField ℚ_[q] (PadicAlgCl q)) (G : Type) [Group G] [MulSemiringAction G L]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (M : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] M] (hLM : L ≤ M)
    (H : Type) [Group H] [Finite H] [MulSemiringAction H M] [FaithfulSMul H M] [MulDistribMulAction H (↥M)ˣ]
    (NL Nn : Subgroup H) [NL.Normal] [Nn.Normal] (e : G ≃* H ⧸ NL) (φ : H) (π : (↥M)ˣ) : Prop where
  smul_algebraMap : ∀ (h : H) (x : ℚ_[q]), h • algebraMap ℚ_[q] M x = algebraMap ℚ_[q] M x
  coe_smul_units : ∀ (h : H) (u : (↥M)ˣ), ((h • u : (↥M)ˣ) : M) = h • (u : M)
  mem_base_iff : ∀ x : M, (x : PadicAlgCl q) ∈ K ↔ ∀ h : H, h • x = x
  mem_layer_iff : ∀ x : M, (x : PadicAlgCl q) ∈ L ↔ ∀ h ∈ NL, h • x = x
  coe_smul_eq : ∀ (g : G) (h : H), (QuotientGroup.mk h : H ⧸ NL) = e g →
    ∀ x : L, ((g • x : L) : PadicAlgCl q) = ((h • (⟨(x : PadicAlgCl q), hLM x.2⟩ : M) : M) : PadicAlgCl q)
  card_quotient : Nat.card (H ⧸ Nn) = Nat.card G
  mem_zpowers : ∀ h : H ⧸ Nn, h ∈ Subgroup.zpowers (QuotientGroup.mk' Nn φ)
  frobenius : ∀ x : M, (∀ h ∈ Nn, h • x = x) → ‖(x : PadicAlgCl q)‖ ≤ 1 →
    ‖((φ • x : M) : PadicAlgCl q) - (x : PadicAlgCl q) ^ Nat.card (IsLocalRing.ResidueField (Rw q K))‖ < 1
  smul_pi : ∀ h : H, h • π = π
  pi_mem : ((π : M) : PadicAlgCl q) ∈ K
  norm_pi_lt : ‖((π : M) : PadicAlgCl q)‖ < 1
  norm_le_norm_pi : ∀ y : M, (∀ h ∈ Nn, h • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖((π : M) : PadicAlgCl q)‖

namespace IsUnramOverlayerDatum

variable {q}
variable {L : IntermediateField ℚ_[q] (PadicAlgCl q)} {G : Type} [Group G] [MulSemiringAction G L]
    {K : IntermediateField ℚ_[q] (PadicAlgCl q)} [FiniteDimensional ℚ_[q] K]
    {M : IntermediateField ℚ_[q] (PadicAlgCl q)} [FiniteDimensional ℚ_[q] M] {hLM : L ≤ M}
    {H : Type} [Group H] [Finite H] [MulSemiringAction H M] [FaithfulSMul H M] [MulDistribMulAction H (↥M)ˣ]
    {NL Nn : Subgroup H} [NL.Normal] [Nn.Normal] {e : G ≃* H ⧸ NL} {φ : H} {π : (↥M)ˣ}


end IsUnramOverlayerDatum


end ExtCitation.LocalLevel
