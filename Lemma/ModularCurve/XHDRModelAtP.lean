import Mathlib
import Lemma.ModularCurve.XHDifferentialsModL
import Lemma.ModularCurve.XHOperators
import Abbrev.ModularCurve_IgusaScheme
import Lemma.AlgebraicCurve.TwoChartIntegralModel
import Lemma.AlgebraicCurve.CurveModel
import Lemma.AlgebraicGeometry.NeronModelPropertyBundleCarrier
import Abbrev.ModularCurve_XHDRModelAtP
import Instance.ModularCurve_XHDRModelAtP
import Structure.ModularCurve_XHDRModelAtP

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open scoped MatrixGroups

namespace ModularCurve

namespace XHDRLevel


theorem jqModC_rat_ne_zero : jqModC ℚ ≠ 0 := fun h =>
  IgusaScheme.jFull_ne_zero 1 (Subtype.ext h)

def jAt (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    ↥(qExpFunctionFieldC ℚ Γ) :=
  ⟨jqModC ℚ, qExpFunctionFieldC_mono ℚ le_top hj⟩

@[simp] theorem coe_jAt (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    (jAt Γ hj : LaurentSeries ℚ) = jqModC ℚ := rfl

variable (p : ℕ) (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

abbrev X : Scheme.{0} := TwoChartIntegralModel (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)


abbrev ιFin := TwoChartIntegralModel.ιFin (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)
abbrev ιInf := TwoChartIntegralModel.ιInf (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)
abbrev jChartFin : ↥(chartAlgFin p Γ hj) := TwoChartIntegralModel.jChartFin (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)

variable {p Γ hj}


def fibreMap {Γ' : Subgroup SL(2, ℤ)} (φ : SchemeHomOver (toBase p Γ hj) (toBase p Γ' hj))
    {κ : Type} [CommRing κ] (toκ : R p →+* κ) : fibre (Γ := Γ) (hj := hj) toκ ⟶ fibre (Γ := Γ') (hj := hj) toκ :=
  pullback.map _ _ _ _ φ.1 (𝟙 _) (𝟙 _) (by rw [φ.2, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])


end XHDRLevel

open XHDRLevel

section

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))


end

namespace XHDRModelAtP

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)


theorem nodePair_mem (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1))) :
    (𝔛.placeOn0 A hA ρ hρ n, 𝔛.placeOn1 A hA ρ hρ n) ∈ ssNodePairsQExp (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p :=
  frob_mk_mem_ssNodePairsQExp (𝔛.nodeEquiv A hA ρ hρ n).2

def πw : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓN p M H hpM) hj) :=
  ⟨𝔛.w.hom ≫ 𝔛.π.1, by rw [Category.assoc, 𝔛.π.2, 𝔛.w_over]⟩

@[simp] theorem πw_val : 𝔛.πw.1 = 𝔛.w.hom ≫ 𝔛.π.1 := rfl

end XHDRModelAtP

end ModularCurve

end
