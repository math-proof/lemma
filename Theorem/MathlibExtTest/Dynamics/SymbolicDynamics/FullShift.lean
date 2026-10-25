/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Dynamics/SymbolicDynamics/FullShift.lean -/

import Def.Dynamics.SymbolicDynamics.FullShift
import Lemma.Set.SymbolicDynamics.FullShift
open SymbolicDynamics.FullShift


example (N : ℕ) (x : FullShiftSpace N) (i : ℤ) :
    unitShift N x i = x (1 + i) := by
  rw [unitShift_apply]

example (N : ℕ) (x : FullShiftSpace N) :
    shiftHomeomorph N x = unitShift N x := by
  rw [shiftHomeomorph_apply]

example (N : ℕ) (x : FullShiftSpace N) (i : ℤ) :
    (shiftHomeomorph N).symm x i = x (-1 + i) := by
  rw [shiftHomeomorph_symm_apply]

example (N : ℕ) : IsOneDimensionalCA N id := by
  rw [isOneDimensionalCA_iff]
  exact ⟨continuous_id, fun _ => rfl⟩

example (N : ℕ) (f : FullShiftSpace N → FullShiftSpace N) (x : FullShiftSpace N) :
    x ∈ jointlyPeriodicPoints N f ↔
      x ∈ Function.periodicPts f ∧ x ∈ Function.periodicPts (unitShift N) := by
  rw [mem_jointlyPeriodicPoints]

example (N : ℕ) : shiftHomeomorph N ∈ automorphismGroup N := by
  rw [automorphismGroup, Subgroup.mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  subst g
  rfl

