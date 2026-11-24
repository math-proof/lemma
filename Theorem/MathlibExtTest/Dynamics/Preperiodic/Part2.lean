module
public import Def.Dynamics.Preperiodic.Part2
public import Theorem.Set.Preperiodic
public import Lean.Elab.Tactic.Omega
public import Def.MathlibExtTest.Dynamics.Preperiodic


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Dynamics/Preperiodic.lean -/

example : Function.IsPeriodicPt swap 2 true := by
  rfl

example : ¬Function.IsPeriodicPt swap 1 true := by
  decide

example : false ∈ Function.forwardOrbit swap true :=
  ⟨1, rfl⟩

example : Function.IsPreperiodicPt swap true := by
  rw [Function.isPreperiodicPt_iff_exists_eq_iterate]
  exact ⟨0, 2, by omega, rfl⟩

