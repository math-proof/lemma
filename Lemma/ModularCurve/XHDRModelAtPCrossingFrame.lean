import Mathlib
import Abbrev.ModularCurve_XHDRModelAtP
import Abbrev.ModularCurve_DRModelPackageCrossingFrame
import Abbrev.ModularCurve_XHDRModelAtPCrossingFrame
import Def.ModularCurve_XHDRModelAtPCrossingFrame

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve
open scoped MatrixGroups

noncomputable section

namespace ModularCurve

namespace XHDRLevel

variable {p : ℕ} (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))


@[reassoc (attr := simp)]
theorem bcMap_fst {O : Type} [CommRing O] (ρO : R p →+* O) {κ : Type} [CommRing κ] (toκ : O →+* κ)
    {toκ' : R p →+* κ} (h : toκ.comp ρO = toκ') :
    bcMap Γ hj ρO toκ h ≫ pullback.fst _ _ = pullback.fst _ _ := by
  rw [bcMap, pullback.map, pullback.lift_fst, Category.comp_id]

@[reassoc (attr := simp)]
theorem bcMap_snd {O : Type} [CommRing O] (ρO : R p →+* O) {κ : Type} [CommRing κ] (toκ : O →+* κ)
    {toκ' : R p →+* κ} (h : toκ.comp ρO = toκ') :
    bcMap Γ hj ρO toκ h ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ) := by
  rw [bcMap, pullback.map, pullback.lift_snd]

end XHDRLevel

open XHDRLevel

namespace XHDRModelAtP

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
  (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
  {O : Type} [CommRing O] (ρO : R p →+* O)
  (toκ : O →+* IsLocalRing.ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)

omit [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)] in

theorem efib_genericPoint_specializes [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (c : ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) :
    letI := (𝔛.Mfib A hA ρ hρ).isIntegral
    (𝔛.efib A hA ρ hρ).base (genericPoint (𝔛.Mfib A hA ρ hρ).C) ⤳ c := by
  letI := (𝔛.Mfib A hA ρ hρ).isIntegral
  have hc : (𝔛.efib A hA ρ hρ).base ((inv (𝔛.efib A hA ρ hρ)).base c) = c := by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl
  rw [← hc]
  exact (genericPoint_specializes _).map (Scheme.Hom.continuous _)

end XHDRModelAtP

end ModularCurve

end
