/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Dynamics/Preperiodic.lean -/

import Def.Dynamics.Preperiodic.Part2
import Lemma.Set.Preperiodic
import Lean.Elab.Tactic.Omega


example : Function.forwardOrbit (id : ℕ → ℕ) 5 = {5} := by
  ext y
  simp [Function.forwardOrbit]

example : Function.IsPreperiodicPt (fun x : ℕ => x) 5 := by
  rw [Function.isPreperiodicPt_iff_exists_eq_iterate]
  exact ⟨0, 1, Nat.zero_lt_one, rfl⟩

example : (5 : ℕ) ∈ Function.periodicPts id :=
  Function.mk_mem_periodicPts Nat.zero_lt_one (Function.is_periodic_id 1 5)

example : ¬Function.IsStrictlyPreperiodicPt id (5 : ℕ) := by
  rintro ⟨_, hnot⟩
  exact hnot (Function.mk_mem_periodicPts Nat.zero_lt_one (Function.is_periodic_id 1 5))

example : Function.IsPreperiodicPt (fun _ : ℕ => 0) 7 := by
  rw [Function.isPreperiodicPt_iff_exists_eq_iterate]
  exact ⟨1, 2, by omega, rfl⟩

example : Function.IsPreperiodicPtOfType (fun _ : ℕ => (0 : ℕ)) 1 1 7 := by
  constructor
  · omega
  · rfl

