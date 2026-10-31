import Def.Analysis.Real.Limits.Basic
import Initialize.Tactic.Attr.Basic
open Set Filter


@[path]
private lemma main
  {f : ℝ → ℝ}
  {x₀ δ a : ℝ}
-- given
  (hδ : δ > 0)
  (hlim : lim [x → x₀] f x = a)
  (hge : ∀ x ∈ Ioc (x₀ - δ) x₀, f x ≥ 0) :
-- imply
  a ≥ 0 := by
-- proof
  have hleft : Tendsto f (nhdsWithin x₀ (Iio x₀)) (nhds a) :=
    hlim.mono_left (nhdsWithin_mono _ fun x hx => ne_of_lt hx)
  refine ge_of_tendsto hleft ?_
  filter_upwards [Ioo_mem_nhdsLT (sub_lt_self x₀ hδ)] with x hx
  exact hge x ⟨hx.1, hx.2.le⟩


-- created on 2023-10-15
-- updated on 2026-10-26
