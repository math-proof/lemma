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
public import Structure.GameTheory.SpragueGrundy

public section

namespace MetaMathlibExt.SpragueGrundy

theorem wfRel (G : ImpartialGame) :
    WellFounded (fun a b => a ∈ G.moves b) := by
  refine Subrelation.wf ?_ (measure G.rank).wf
  intro a b h
  exact G.rank_lt b a h

end MetaMathlibExt.SpragueGrundy
