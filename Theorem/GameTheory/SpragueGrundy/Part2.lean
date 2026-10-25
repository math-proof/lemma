/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SpragueGrundy.lean -/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.WellFounded
import Mathlib.Order.Lattice.Nat
import Def.GameTheory.SpragueGrundy


namespace MetaMathlibExt.SpragueGrundy

theorem exists_not_mem (s : Finset ℕ) : ∃ n, n ∉ s := by
  refine ⟨s.sup id + 1, fun h => ?_⟩
  have hle : id (s.sup id + 1) ≤ s.sup id := Finset.le_sup (f := id) h
  simp only [id_eq] at hle
  omega

end MetaMathlibExt.SpragueGrundy
