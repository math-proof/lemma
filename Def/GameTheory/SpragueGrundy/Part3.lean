/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SpragueGrundy.lean -/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.WellFounded
import Mathlib.Order.Lattice.Nat
import Theorem.GameTheory.SpragueGrundy.Part3


namespace MetaMathlibExt.SpragueGrundy

noncomputable def grundy (G : ImpartialGame) : G.Pos → ℕ :=
  (wfRel G).fix fun p ih =>
    mex ((G.moves p).attach.image (fun x => ih x.val x.property))

end MetaMathlibExt.SpragueGrundy
