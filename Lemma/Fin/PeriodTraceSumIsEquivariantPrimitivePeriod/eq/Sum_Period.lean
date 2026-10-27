import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.ModularCurve.PeriodMap
import Lemma.ModularCurve.PeriodTransfer
import Lemma.Int.P2MUtil

open scoped MatrixGroups
open ModularCurve.Period

/--
[ModularCurve_Period_traceSum_period_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_Period_traceSum_period_eq.lean)
-/
@[path]
private lemma main
  :
-- imply
  ∀ {Γ Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}
    {F : UpperHalfPlane → ℂ} [inst : Fintype (↥Γ ⧸ Δ.subgroupOf Γ)]
    (hF : ModularCurve.Period.IsEquivariantPrimitive Δ F) (γ : ↥Γ),
    (ModularCurve.Period.IsEquivariantPrimitive.traceSum hF).period γ =
      ∑ q, hF.period (ModularCurve.Period.transferElt γ q) := by
-- proof
  intro Γ Δ F inst hF γ
  rw [← IsEquivariantPrimitive.sub_eq_period hF.traceSum γ UpperHalfPlane.I]
  exact sum_traceRep_smul_sub hF γ UpperHalfPlane.I


-- created on 2026-10-23
