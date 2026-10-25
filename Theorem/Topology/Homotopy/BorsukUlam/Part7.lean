/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.BallSphere
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.UniformSpace.HeineCantor
import Def.Topology.Homotopy.BorsukUlam.Part10


namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

/-- The lift never hits the origin. -/
theorem buV_ne_zero {n : ℕ} (x : Fin n → ℝ) : buV n x ≠ 0 := by
  rw [buV]
  intro hcon
  have hcon' : Fin.cons (α := fun _ => ℝ) (1 - ‖x‖) x = (0 : Fin (n + 1) → ℝ) := by
    have h2 := congrArg WithLp.ofLp hcon
    simpa [WithLp.ofLp_toLp] using h2
  have hhead : (1 : ℝ) - ‖x‖ = 0 := by
    have h0 := congrFun hcon' (0 : Fin (n + 1))
    rw [Fin.cons_zero, Pi.zero_apply] at h0
    exact h0
  have hnorm : ‖x‖ = 1 := by
    have h := sub_eq_zero.mp hhead
    exact h.symm
  have hx0 : x ≠ 0 := by
    intro hx
    rw [hx, norm_zero] at hnorm
    exact zero_ne_one hnorm
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx0
  have htail := congrFun hcon' i.succ
  rw [Fin.cons_succ, Pi.zero_apply] at htail
  exact hi htail

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
