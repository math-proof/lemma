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
public import Theorem.GameTheory.SpragueGrundy.Part2

@[expose] public section

namespace MetaMathlibExt.SpragueGrundy

noncomputable def mex (s : Finset ℕ) : ℕ := Nat.find (exists_not_mem s)

end MetaMathlibExt.SpragueGrundy
