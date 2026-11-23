/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/WordAlgebra.lean -/
module

public import Mathlib.Algebra.FreeAlgebra
public import Theorem.NumberTheory.MultipleZeta.Index.Part2
public import Theorem.Nat.MultipleZeta.Index
public import Def.NumberTheory.MultipleZeta.WordAlgebra

public section

namespace MetaMathlibExt.MultipleZeta

theorem pnatEntries_val (idx : Index) :
    idx.pnatEntries.map PNat.val = idx.entries := by
  rcases idx with ⟨_, c⟩
  unfold Index.pnatEntries Index.entries
  rw [List.map_map]
  change c.blocks.attach.map (fun x => x.1) = c.blocks
  exact List.attach_map_subtype_val c.blocks

end MetaMathlibExt.MultipleZeta
