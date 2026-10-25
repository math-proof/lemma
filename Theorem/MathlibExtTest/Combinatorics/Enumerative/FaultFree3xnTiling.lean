/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/FaultFree3xnTiling.lean -/


import Def.Combinatorics.Enumerative.FaultFree3xnTiling.Part21
import Lemma.Finset.Enumerative.FaultFree3xnTiling
import Mathlib.Tactic.NormNum


namespace MathlibExtTest.Combinatorics.Enumerative.FaultFree3xnTiling

-- The classification recognizes a concrete horizontal domino.
example :
    MetaMathlibExt.IsSquareOrDomino
      ({((0 : Fin 3), (0 : Fin 2)), ((0 : Fin 3), (1 : Fin 2))} :
        Finset (MetaMathlibExt.TilingCell 2)) := by
  rw [MetaMathlibExt.isSquareOrDomino_iff]
  exact Or.inr ⟨((0 : Fin 3), (0 : Fin 2)), ((0 : Fin 3), (1 : Fin 2)),
    by decide, by simp [MetaMathlibExt.TilingCell.Adjacent], rfl⟩

-- The recurrence theorem computes the first value beyond its initial conditions.
example (h : 1 ≤ (7 : ℕ)) : MetaMathlibExt.verticalFaultFreeTilingCount 7 = 904 := by
  have hrec := MetaMathlibExt.fault_free_3xn_tiling_recursion 7 h
  norm_num [MetaMathlibExt.tilingCount] at hrec
  exact_mod_cast hrec

end MathlibExtTest.Combinatorics.Enumerative.FaultFree3xnTiling
