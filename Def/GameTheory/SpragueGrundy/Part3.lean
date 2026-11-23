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
public import Theorem.GameTheory.SpragueGrundy.Part3

@[expose] public section

namespace MetaMathlibExt.SpragueGrundy

noncomputable def grundy (G : ImpartialGame) : G.Pos → ℕ :=
  (wfRel G).fix fun p ih =>
    mex ((G.moves p).attach.image (fun x => ih x.val x.property))

end MetaMathlibExt.SpragueGrundy
