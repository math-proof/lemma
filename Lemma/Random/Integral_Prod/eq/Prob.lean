import sympy.stats.joint_rv
import sympy.Basic
open MeasureTheory


/--
Chapman–Kolmogorov marginalization of a Markov chain: integrating the initial
density times the product of one-step transition densities over the first `n`
states yields the marginal density of the `n`-th state:

  ∫ Pr(s₀ = u₀) · ∏_{t<n} Pr(s_{t+1} = u_{t+1} | s_t = u_t) du₀…du_{n-1} = Pr(sₙ = v)

Python: Random.Integral_Prod.eq.Prob.
-/
@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  {π : Measure Ω}
  {s : ℕ → Ω → α}
  {n : ℕ} [SinglePSpace π (s 0)] [SinglePSpace π (s n)]
-- given
  (hT : ∀ t : ℕ, SinglePSpace π (s (t + 1), s t))
  (v : α) :
-- imply
  ∫⁻ u : Fin n → α,
      let path : Fin (n + 1) → α := Fin.snoc u v
      π.prob (s 0) (path 0) *
        ∏ t : Fin n,
          @MeasureTheory.Measure.condProb Ω α α _ _ _ π (s (t.val + 1), s t.val) (hT t.val)
            (path t.succ, path t.castSucc)
    ∂(Measure.pi fun _ : Fin n => ReferenceMeasure.measure) =
  π.prob (s n) v := by
-- proof
  sorry


-- created on 2026-10-01
