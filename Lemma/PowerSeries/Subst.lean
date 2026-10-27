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
  {F' F : FormalGroup R}
  {ψ : FormalGroup.LawHom F' F}
  {n : ℕ} :
-- imply
  PowerSeries.subst (F'.nthSeries n) ψ.series = PowerSeries.subst ψ.series (F.nthSeries n) := by
  classical
    have hψ0 : PowerSeries.constantCoeff ψ.series = 0 := ψ.constantCoeff_series
    have hψ : PowerSeries.HasSubst ψ.series := PowerSeries.HasSubst.of_constantCoeff_zero' hψ0
    have hψc : MvPowerSeries.HasSubst (fun _ : Unit => ψ.series) := PowerSeries.HasSubst.const hψ
    induction n with
    | zero =>
      rw [FormalGroup.nthSeries_zero, FormalGroup.nthSeries_zero, ← PowerSeries.coe_substAlgHom hψ, map_zero]
      ext e
      rw [PowerSeries.coeff_subst' PowerSeries.HasSubst.zero', map_zero]
      apply finsum_eq_zero_of_forall_eq_zero
      intro d
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hψ0, zero_smul]
      · rw [zero_pow hd.ne', map_zero, smul_zero]
    | succ n ih =>
      have hb : MvPowerSeries.HasSubst (![F'.nthSeries n, PowerSeries.X] : Fin 2 → PowerSeries R) :=
        F'.hasSubst_nthSeries n
      have hF' : MvPowerSeries.HasSubst (fun _ : Unit => F'.toPowerSeries) :=
        MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => F'.zero_constantCoeff
      have hsX : ∀ i : Fin 2, MvPowerSeries.constantCoeff (FormalGroup.LawHom.substX i ψ.series) = 0 := by
-- proof
        intro i
        unfold FormalGroup.LawHom.substX
        exact PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ hψ0
      have hS : MvPowerSeries.HasSubst (![FormalGroup.LawHom.substX 0 ψ.series, FormalGroup.LawHom.substX 1 ψ.series] :
          Fin 2 → MvPowerSeries (Fin 2) R) :=
        MvPowerSeries.hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.mpr ⟨hsX 0, hsX 1⟩)
      have key := congrArg (MvPowerSeries.subst (![F'.nthSeries n, PowerSeries.X] : Fin 2 → PowerSeries R)) ψ.comm
      have eL : MvPowerSeries.subst (![F'.nthSeries n, PowerSeries.X] : Fin 2 → PowerSeries R)
        (PowerSeries.subst F'.toPowerSeries ψ.series) = PowerSeries.subst (F'.nthSeries (n + 1)) ψ.series := by
        rw [PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply hF' hb, FormalGroup.nthSeries_succ]
        rfl
      have eXi : ∀ i : Fin 2, MvPowerSeries.subst (![F'.nthSeries n, PowerSeries.X] : Fin 2 → PowerSeries R)
        (FormalGroup.LawHom.substX i ψ.series) =
        PowerSeries.subst ((![F'.nthSeries n, PowerSeries.X] : Fin 2 → PowerSeries R) i) ψ.series := by
        intro i
        unfold FormalGroup.LawHom.substX
        rw [PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply
          (MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X i) hb,
          MvPowerSeries.subst_X hb]
        rfl
      have eR : MvPowerSeries.subst (![F'.nthSeries n, PowerSeries.X] : Fin 2 → PowerSeries R)
        (MvPowerSeries.subst ![FormalGroup.LawHom.substX 0 ψ.series, FormalGroup.LawHom.substX 1 ψ.series]
          F.toPowerSeries) =
        MvPowerSeries.subst ![PowerSeries.subst ψ.series (F.nthSeries n), ψ.series] F.toPowerSeries := by
        rw [MvPowerSeries.subst_comp_subst_apply hS hb]
        congr 1
        funext i
        fin_cases i
        ·
          show MvPowerSeries.subst _ (FormalGroup.LawHom.substX 0 ψ.series) = _
          rw [eXi 0]; show PowerSeries.subst (F'.nthSeries n) ψ.series = _; rw [ih]; rfl
        ·
          show MvPowerSeries.subst _ (FormalGroup.LawHom.substX 1 ψ.series) = _
          rw [eXi 1]; show PowerSeries.subst PowerSeries.X ψ.series = _; rw [PowerSeries.X_subst]; rfl
      have eG : PowerSeries.subst ψ.series (F.nthSeries (n + 1)) =
          MvPowerSeries.subst ![PowerSeries.subst ψ.series (F.nthSeries n), ψ.series] F.toPowerSeries := by
        rw [FormalGroup.nthSeries_succ, PowerSeries.subst,
          MvPowerSeries.subst_comp_subst_apply (F.hasSubst_nthSeries n) hψc]
        congr 1
        funext i
        fin_cases i
        · rfl
        · show MvPowerSeries.subst (fun _ : Unit => ψ.series) PowerSeries.X = ψ.series
          exact PowerSeries.subst_X hψ
      rw [← eL, key, eR, eG]


-- created on 2026-10-23
