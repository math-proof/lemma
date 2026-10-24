import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.FiniteAbelianDual
open scoped DirectSum
open MathlibExt.GroupTheory.FiniteAbelianDualWanted


/--
[finite_abelian_dual_iso](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/FiniteAbelianDual.lean)
-/
@[path]
private lemma finite_abelian_dual_iso
  [AddCommGroup α] [Finite α] :
-- imply
  Nonempty (α ≃+ AddChar α ℂ) := by
-- proof
  obtain ⟨ι, _, n, hn, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' α
  classical
  let _ : ∀ i, NeZero (n i) := fun i => ⟨by
    have := hn i
    positivity⟩
  let precomp : AddChar (⨁ i, ZMod (n i)) ℂ ≃+ AddChar α ℂ :=
    { toFun := fun (ψ : AddChar (⨁ i, ZMod (n i)) ℂ) =>
        AddChar.compAddMonoidHom ψ e.toAddMonoidHom
      invFun := fun (ψ : AddChar α ℂ) =>
        AddChar.compAddMonoidHom ψ e.symm.toAddMonoidHom
      left_inv := fun ψ => by
        ext x
        simp
      right_inv := fun ψ => by
        ext x
        simp
      map_add' := fun _ _ => by
        ext x
        rfl }
  exact ⟨e.trans <| (dual_zmodDirectSumEquiv n).trans precomp⟩

/--
[dual_prod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/FiniteAbelianDual.lean)
-/
@[path]
private lemma dual_prod
  [AddCommGroup α] [AddCommGroup β] :
-- imply
  Nonempty (AddChar (α × β) ℂ ≃+ (AddChar α ℂ × AddChar β ℂ)) :=
-- proof
  ⟨dual_prodEquiv α β⟩


-- created on 2026-10-20
-- updated on 2026-10-24
