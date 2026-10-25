/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/FiniteAbelianDual.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Algebra.Group.AddChar
import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Theorem.GroupTheory.FiniteAbelianDual


namespace MathlibExt.GroupTheory.FiniteAbelianDualWanted

open scoped DirectSum

noncomputable def dual_zmodDirectSumEquiv {ι : Type*} [Fintype ι]
    (n : ι → ℕ) [∀ i, NeZero (n i)] :
    (⨁ i, ZMod (n i)) ≃+ AddChar (⨁ i, ZMod (n i)) ℂ := by
  classical
  letI : Fintype (⨁ i, ZMod (n i)) :=
    Fintype.ofEquiv (∀ i, ZMod (n i)) (DirectSum.addEquivProd _).symm.toEquiv
  refine AddEquiv.ofBijective (dual_zmodDirectSumHom n) ?_
  rw [Fintype.bijective_iff_injective_and_card, AddChar.card_eq]
  exact ⟨dual_zmodDirectSumHom_injective n, rfl⟩

def dual_prodEquiv (α β : Type*) [AddCommGroup α] [AddCommGroup β] :
    AddChar (α × β) ℂ ≃+ (AddChar α ℂ × AddChar β ℂ) where
  toFun ψ :=
    (ψ.compAddMonoidHom (AddMonoidHom.inl α β),
      ψ.compAddMonoidHom (AddMonoidHom.inr α β))
  invFun χ :=
    { toFun := fun x => χ.1 x.1 * χ.2 x.2
      map_zero_eq_one' := by simp
      map_add_eq_mul' := by
        intro x y
        simp only [Prod.fst_add, Prod.snd_add, AddChar.map_add_eq_mul]
        ac_rfl }
  left_inv ψ := by
    ext x
    rcases x with ⟨x, y⟩
    change ψ (x, 0) * ψ (0, y) = ψ (x, y)
    rw [← AddChar.map_add_eq_mul]
    simp
  right_inv χ := by
    ext x <;> simp
  map_add' ψ χ := by
    ext x <;> rfl

end MathlibExt.GroupTheory.FiniteAbelianDualWanted
