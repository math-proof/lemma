module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Def.Topology.Homotopy.BorsukUlam.Part10


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
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
