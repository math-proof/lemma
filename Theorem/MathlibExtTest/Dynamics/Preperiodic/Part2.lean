/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Dynamics/Preperiodic.lean -/

import Def.Dynamics.Preperiodic.Part2
import Lemma.Set.Preperiodic
import Lean.Elab.Tactic.Omega
import Def.MathlibExtTest.Dynamics.Preperiodic


example : Function.IsPeriodicPt swap 2 true := by
  rfl

example : ¬Function.IsPeriodicPt swap 1 true := by
  decide

example : false ∈ Function.forwardOrbit swap true :=
  ⟨1, rfl⟩

example : Function.IsPreperiodicPt swap true := by
  rw [Function.isPreperiodicPt_iff_exists_eq_iterate]
  exact ⟨0, 2, by omega, rfl⟩

