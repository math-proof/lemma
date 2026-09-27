import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import sympy.dynamics.actor_critic
import sympy.Basic


@[main]
private lemma main
-- given
  (d : ℕ)
  (r : ℝ) :
-- imply
  IsCompact (actor_box d r) := by
-- proof
  have h : actor_box d r = WithLp.toLp 2 '' Set.Icc (fun _ => -r) (fun _ => r) := by
    ext θ
    constructor
    · intro hθ
      exact ⟨WithLp.ofLp θ, ⟨fun j => (abs_le.1 (hθ j)).1, fun j => (abs_le.1 (hθ j)).2⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩ j
      exact abs_le.2 ⟨hx.1 j, hx.2 j⟩
  rw [h]
  exact isCompact_Icc.image (PiLp.continuous_toLp 2 _)


-- created on 2026-09-26
