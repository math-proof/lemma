/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SpragueGrundy.lean -/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.WellFounded
import Mathlib.Order.Lattice.Nat
import Theorem.GameTheory.SpragueGrundy.Part2


namespace MetaMathlibExt.SpragueGrundy

noncomputable def mex (s : Finset ℕ) : ℕ := Nat.find (exists_not_mem s)

end MetaMathlibExt.SpragueGrundy
