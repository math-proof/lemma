/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/WordAlgebra.lean -/

import Mathlib.Algebra.FreeAlgebra
import Theorem.NumberTheory.MultipleZeta.Index.Part2
import Lemma.Nat.MultipleZeta.Index
import Def.NumberTheory.MultipleZeta.WordAlgebra


namespace MetaMathlibExt.MultipleZeta

theorem pnatEntries_val (idx : Index) :
    idx.pnatEntries.map PNat.val = idx.entries := by
  rcases idx with ⟨_, c⟩
  unfold Index.pnatEntries Index.entries
  rw [List.map_map]
  change c.blocks.attach.map (fun x => x.1) = c.blocks
  exact List.attach_map_subtype_val c.blocks

end MetaMathlibExt.MultipleZeta
