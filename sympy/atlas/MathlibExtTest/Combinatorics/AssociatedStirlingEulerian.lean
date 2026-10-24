/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/AssociatedStirlingEulerian.lean -/

-- Author: @toskua, Avocado

import sympy.atlas.Combinatorics.AssociatedStirlingEulerian

open MetaMathlibExt

-- Excedance counts on small perms.
example : excedanceCount 0 (1 : Equiv.Perm (Fin 0)) = 0 := by decide
example : excedanceCount 1 (1 : Equiv.Perm (Fin 1)) = 0 := by decide
example : excedanceCount 2 (1 : Equiv.Perm (Fin 2)) = 0 := by decide
example : excedanceCount 2 (Equiv.swap (0 : Fin 2) 1) = 1 := by decide

example : IsRMinusAssociatedCyclePerm 2 1 (1 : Equiv.Perm (Fin 1)) := by
  unfold IsRMinusAssociatedCyclePerm
  simp

example : IsRAssociatedCyclePerm 1 2 (Equiv.swap (0 : Fin 2) 1) := by
  unfold IsRAssociatedCyclePerm
  constructor
  · decide
  · have hcycle : (Equiv.swap (0 : Fin 2) 1).IsCycle :=
      Equiv.Perm.isCycle_swap (by decide)
    have hsupp : (Equiv.swap (0 : Fin 2) 1).support.card = 2 := by decide
    have hct : (Equiv.swap (0 : Fin 2) 1).cycleType = {2} := by
      rw [hcycle.cycleType, hsupp]
    rw [hct]
    simp

example : rMinusAssociatedStirlingEulerian 2 0 1 = 0 := by
  have hQ : ∀ σ : Equiv.Perm (Fin 0), excedanceCount 0 σ ≠ 1 := by decide
  unfold rMinusAssociatedStirlingEulerian
  simp [hQ]
