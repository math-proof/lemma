import sympy.functions.elementary.exponential
import sympy.series.limits


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : ¬x → ∞) :
-- imply
  stdPart x.exp = (stdPart x).exp := by
-- proof
  have hx := not_lt.mp h
  have h_tendsto : x.Tendsto (nhds (stdPart x)) := by
    rw [tendsto_iff_forall]
    constructor <;>
      intro s hs
    ·
      exact (ArchimedeanClass.lt_of_lt_stdPart Hyperreal.coeRingHom hx hs).le
    ·
      exact (ArchimedeanClass.lt_of_stdPart_lt Hyperreal.coeRingHom hx hs).le
  simpa [Hyperreal.exp] using stdPart_of_tendsto (stdPart_map Real.continuous_exp.continuousAt h_tendsto)


-- created on 2025-12-27
