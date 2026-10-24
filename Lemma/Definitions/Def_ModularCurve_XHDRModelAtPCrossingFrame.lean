import Mathlib
import Lemma.Definitions.Def_ModularCurve_XHDRModelAtP
import Lemma.Definitions.Def_ModularCurve_DRModelPackageCrossingFrame

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve
open scoped MatrixGroups

noncomputable section

namespace ModularCurve

namespace XHDRLevel

variable {p : ℕ} (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

abbrev XO {O : Type} [CommRing O] (ρO : R p →+* O) : Scheme.{0} :=
  pullback (toBase p Γ hj) (Spec.map (CommRingCat.ofHom ρO))

abbrev XO.toBase {O : Type} [CommRing O] (ρO : R p →+* O) : XO Γ hj ρO ⟶ Spec (CommRingCat.of O) :=
  pullback.snd _ _

def bcMap {O : Type} [CommRing O] (ρO : R p →+* O) {κ : Type} [CommRing κ] (toκ : O →+* κ)
    {toκ' : R p →+* κ} (h : toκ.comp ρO = toκ') :
    fibre (Γ := Γ) (hj := hj) toκ' ⟶ XO Γ hj ρO :=
  pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom toκ)) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h])

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

variable {Γ hj}

abbrev baseGerm {O : Type} [CommRing O] (ρO : R p →+* O) (x : ↥(XO Γ hj ρO)) (o : O) : (XO Γ hj ρO).presheaf.stalk x :=
  (XO Γ hj ρO).presheaf.germ ⊤ x trivial
    ((XO.toBase Γ hj ρO).appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o))

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

abbrev crossingPt (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1))) : ↥(XO (ΓM M H) hj ρO) :=
  (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n

abbrev ξinf : ↥(XO (ΓM M H) hj ρO) :=
  letI := (𝔛.Mfib A hA ρ hρ).isIntegral
  (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base (genericPoint (𝔛.Mfib A hA ρ hρ).C)

abbrev ξzero : ↥(XO (ΓM M H) hj ρO) :=
  letI := (𝔛.Mfib A hA ρ hρ).isIntegral
  (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base (genericPoint (𝔛.Mfib A hA ρ hρ).C)

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
