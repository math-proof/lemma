import Lemma.AbsoluteValue.Norm.eq.UFn
open AbsoluteValue


@[main, comm, mp, mpr]
private lemma main
  [Field K]
-- given
  (v : AbsoluteValue K ℝ) :
-- imply
  v.IsNontrivial ↔ ∃ x : v.Completion, 1 < ‖x‖ := by
-- proof
  refine ⟨fun hnt => ?_, fun h => ?_⟩
  ·
    obtain ⟨x, hx⟩ := hnt.exists_abv_gt_one
    exact ⟨(x : v.Completion), by rwa [Norm.eq.UFn]⟩
  ·
    obtain ⟨c, hc⟩ := h
    obtain ⟨x, hx⟩ : ∃ x : K, ‖(c - (x : v.Completion) : v.Completion)‖ < (‖c‖ - 1) / 2 := by
      have hε : (0 : ℝ) < (‖c‖ - 1) / 2 := by positivity
      obtain ⟨w, hw⟩ := UniformSpace.Completion.denseRange_coe (α := WithAbs v) |>.exists_dist_lt c hε
      rw [dist_eq_norm] at hw
      obtain ⟨x, rfl⟩ := WithAbs.toAbs_surjective v w
      exact ⟨x, hw⟩
    have hkey : ‖(x : v.Completion)‖ > 1 := by
      have heq : (c - (x : v.Completion) : v.Completion) + (x : v.Completion) = c := sub_add_cancel ..
      have htri := heq ▸ norm_add_le (c - (x : v.Completion) : v.Completion) (x : v.Completion)
      linarith
    refine ⟨x, ?_, ?_⟩
    · intro hxz
      rw [Norm.eq.UFn] at hkey
      have : v x = 0 := by rw [hxz]; exact AbsoluteValue.map_zero v
      linarith
    · intro hv1
      rw [Norm.eq.UFn] at hkey
      linarith


-- created on 2026-09-19
