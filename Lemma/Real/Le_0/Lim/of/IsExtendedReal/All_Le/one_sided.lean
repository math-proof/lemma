import sympy.series.limits
import sympy.Basic
open Set Filter


@[path]
private lemma main
  {f : ℝ → ℝ}
  {x₀ δ a : ℝ}
-- given
  (hδ : δ > 0)
  (hlim : lim [x → x₀] f x = a)
  (hle : ∀ x ∈ Ico x₀ (x₀ + δ), f x ≤ 0) :
-- imply
  a ≤ 0 := by
-- proof
  have hright : Tendsto f (nhdsWithin x₀ (Ioi x₀)) (nhds a) :=
    hlim.mono_left (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
  refine le_of_tendsto hright ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_add_of_pos_right x₀ hδ)] with x hx
  exact hle x ⟨hx.1.le, hx.2⟩


-- created on 2026-10-11
-- updated on 2026-10-12
