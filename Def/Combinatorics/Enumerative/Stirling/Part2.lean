/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Stirling.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Fin
import Theorem.Combinatorics.Enumerative.Stirling
/-!
# Permutations and unsigned Stirling numbers

This file identifies unsigned Stirling numbers of the first kind with permutations having a
prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

def dropFin {n : ℕ} (q : Fin n) : Fin (n + 1) → Fin n :=
  Fin.cases q id

end MetaMathlibExt
