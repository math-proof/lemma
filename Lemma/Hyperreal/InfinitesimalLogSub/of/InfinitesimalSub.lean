import sympy.functions.elementary.exponential
import sympy.series.limits
import Lemma.Hyperreal.IsSt.is.Le0Mk.EqStdPart
open Hyperreal


@[main]
private lemma main
  {x : ℝ*}
  {r : ℝ}
-- given
  (h_r : r ≠ 0)
  (h : (x - r) → 0) :
-- imply
  (Log.log x - (Real.log r : ℝ)) → 0 := by
-- proof
  obtain ⟨hx, hst⟩ := Le0Mk.EqStdPart.of.IsSt h
  have h_tendsto : x.Tendsto (nhds r) := by
    rw [Hyperreal.tendsto_iff_forall]
    constructor <;>
      intro s hs
    ·
      exact (ArchimedeanClass.lt_of_lt_stdPart Hyperreal.coeRingHom hx (by rwa [hst])).le
    ·
      exact (ArchimedeanClass.lt_of_stdPart_lt Hyperreal.coeRingHom hx (by rwa [hst])).le
  have h_log := Hyperreal.stdPart_map (Real.continuousAt_log h_r) h_tendsto
  have h_nonneg := Hyperreal.archimedeanClassMk_nonneg_of_tendsto h_log
  exact IsSt.of.Le0Mk.EqStdPart h_nonneg (Hyperreal.stdPart_of_tendsto h_log)


-- created on 2026-10-01
