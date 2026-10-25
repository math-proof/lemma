import Mathlib
import Instance.ExtCitation_LocalLevelResidues
import Def.GroupCohomology_CyclicCarry
import Structure.ExtCitation_LocalLevel_FundamentalClass

set_option autoImplicit false

open CategoryTheory groupCohomology

namespace ExtCitation.LocalLevel

variable (q : ℕ) [Fact q.Prime]


namespace IsUnramOverlayerDatum

variable {q}
variable {L : IntermediateField ℚ_[q] (PadicAlgCl q)} {G : Type} [Group G] [MulSemiringAction G L]
    {K : IntermediateField ℚ_[q] (PadicAlgCl q)} [FiniteDimensional ℚ_[q] K]
    {M : IntermediateField ℚ_[q] (PadicAlgCl q)} [FiniteDimensional ℚ_[q] M] {hLM : L ≤ M}
    {H : Type} [Group H] [Finite H] [MulSemiringAction H M] [FaithfulSMul H M] [MulDistribMulAction H (↥M)ˣ]
    {NL Nn : Subgroup H} [NL.Normal] [Nn.Normal] {e : G ≃* H ⧸ NL} {φ : H} {π : (↥M)ˣ}

theorem ofMul_pi_mem (d : IsUnramOverlayerDatum q L G K M hLM H NL Nn e φ π) :
    (Additive.ofMul π : Rep.ofMulDistribMulAction H (↥M)ˣ) ∈
      Representation.invariants ((Rep.ofMulDistribMulAction H (↥M)ˣ).ρ.comp Nn.subtype) :=
  fun n => congrArg Additive.ofMul (d.smul_pi (n : H))

def piInv (d : IsUnramOverlayerDatum q L G K M hLM H NL Nn e φ π) : (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn :=
  ⟨Additive.ofMul π, d.ofMul_pi_mem⟩

theorem piInv_val (d : IsUnramOverlayerDatum q L G K M hLM H NL Nn e φ π) :
    (d.piInv.1 : Rep.ofMulDistribMulAction H (↥M)ˣ) = Additive.ofMul π := rfl

end IsUnramOverlayerDatum

def IsLocalFundamentalClass (L : IntermediateField ℚ_[q] (PadicAlgCl q)) (G : Type) [Group G] [MulSemiringAction G L]
    [MulDistribMulAction G (↥L)ˣ] (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction G (↥L)ˣ)) : Prop :=
  ∀ (M : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] M] (hLM : L ≤ M)
    (H : Type) [Group H] [Finite H] [MulSemiringAction H M] [FaithfulSMul H M] [MulDistribMulAction H (↥M)ˣ]
    (NL Nn : Subgroup H) [NL.Normal] [Nn.Normal] (e : G ≃* H ⧸ NL) (φ : H) (π : (↥M)ˣ)
    (d : IsUnramOverlayerDatum q L G K M hLM H NL Nn e φ π)
    (ι : Rep.res (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) (Rep.ofMulDistribMulAction G (↥L)ˣ) ⟶ Rep.ofMulDistribMulAction H (↥M)ˣ),
    (∀ v : (↥L)ˣ, (((Additive.toMul (ι.hom (Additive.ofMul v)) : (↥M)ˣ) : M) : PadicAlgCl q) = ((v : L) : PadicAlgCl q)) →
    ∀ (hfin : IsOfFinOrder (QuotientGroup.mk' Nn φ))
      (hc : carryFun (QuotientGroup.mk' Nn φ) d.mem_zpowers hfin d.piInv ∈ cocycles₂ ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn)),
      (groupCohomology.map (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) ι 2).hom u =
        ((infNatTrans ℤ Nn 2).app (Rep.ofMulDistribMulAction H (↥M)ˣ)).hom
          ((H2π ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn)).hom
            ⟨carryFun (QuotientGroup.mk' Nn φ) d.mem_zpowers hfin d.piInv, hc⟩)

end ExtCitation.LocalLevel
