/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SpragueGrundy.lean -/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.WellFounded
public import Mathlib.Order.Lattice.Nat
public import Def.GameTheory.SpragueGrundy

public section

namespace MetaMathlibExt.SpragueGrundy

theorem exists_not_mem (s : Finset ℕ) : ∃ n, n ∉ s := by
  refine ⟨s.sup id + 1, fun h => ?_⟩
  have hle : id (s.sup id + 1) ≤ s.sup id := Finset.le_sup (f := id) h
  simp only [id_eq] at hle
  omega

end MetaMathlibExt.SpragueGrundy
