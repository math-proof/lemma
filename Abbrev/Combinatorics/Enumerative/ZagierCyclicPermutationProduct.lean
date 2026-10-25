/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.GroupTheory.Perm.Fin
import Def.Combinatorics.Enumerative.Stirling.Part4
import Lemma.Finset.Enumerative.Stirling
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part32
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

abbrev ZagFullPerm (n : ℕ) :=
  {s : Equiv.Perm (Fin n) // cycleQuotientCount s = 1}

abbrev ZagPlanePairs (n k : ℕ) :=
  {p : ZagFullPerm n × Equiv.Perm (Fin n) //
    cycleQuotientCount p.2 = k ∧
      cycleQuotientCount (p.1.1 * p.2⁻¹) = 1}

abbrev ZagPlaneConfigBy (n : ℕ) (hn : 0 < n) (k l : ℕ) :=
  {p : {e : Equiv.Perm (Fin n) //
      e (zagBasePoint ⟨0, hn⟩) = zagBasePoint ⟨0, hn⟩} ×
      Equiv.Perm (Fin n) //
    cycleQuotientCount p.2 = k ∧
      cycleQuotientCount (zagDiagonal p.1.1 p.2) = l}

abbrev ZagPlaneConfig (n : ℕ) (hn : 0 < n) (k : ℕ) :=
  ZagPlaneConfigBy n hn k 1

end MetaMathlibExt
