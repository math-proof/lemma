/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SpragueGrundy.lean -/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.WellFounded
import Mathlib.Order.Lattice.Nat
import Structure.GameTheory.SpragueGrundy


namespace MetaMathlibExt.SpragueGrundy

theorem wfRel (G : ImpartialGame) :
    WellFounded (fun a b => a ∈ G.moves b) := by
  refine Subrelation.wf ?_ (measure G.rank).wf
  intro a b h
  exact G.rank_lt b a h

end MetaMathlibExt.SpragueGrundy
