import Mathlib
import Initialize.Tactic.Attr.Basic
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_PointTransport
open FormalGroup IsLocalRing


/-- ported from external source -/
@[path]
private lemma main
  [CommRing R]
  {I : Ideal R} [IsAdicComplete I R]
  {F : FormalGroup R} :
-- imply
  ∃ ψ : FormalGroup.LawIso F F, ψ.series = PowerSeries.X ∧ ∀ y ∈ I, ψ.toLawHom.appAdic I y = y := by
  classical
    have hF : PowerSeries.HasSubst F.toPowerSeries :=
      PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
    have hXi : ∀ i : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) :=
      fun i => PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
    have hsx : ∀ i : Fin 2, FormalGroup.LawHom.substX i (PowerSeries.X : PowerSeries R) = MvPowerSeries.X i := by
-- proof
      intro i
      unfold FormalGroup.LawHom.substX
      exact PowerSeries.subst_X (hXi i)
    have hvec : (![MvPowerSeries.X (0 : Fin 2), MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) R) =
        MvPowerSeries.X := by
      funext i; fin_cases i <;> rfl
    let ψ : FormalGroup.LawIso F F :=
      { series := PowerSeries.X
        constantCoeff_series := PowerSeries.constantCoeff_X
        comm := by
          rw [PowerSeries.subst_X hF, hsx, hsx, hvec, MvPowerSeries.subst_self, id]
        isUnit_coeff_one := by
          rw [PowerSeries.coeff_one_X]; exact isUnit_one }
    refine ⟨ψ, rfl, fun y _ => ?_⟩
    let : WithIdeal R := ⟨I⟩
    show FormalGroup.evalSeries (PowerSeries.X : PowerSeries R) y = y
    unfold FormalGroup.evalSeries
    exact @PowerSeries.eval₂_X R _ R _ (algebraMap R R) y ⊥ _


-- created on 2026-10-23
