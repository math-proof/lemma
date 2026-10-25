/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.GroupTheory.Perm.Fin
import Def.Combinatorics.Enumerative.Stirling.Part4
import Lemma.Finset.Enumerative.Stirling
import Theorem.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part6
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

noncomputable def zagCycleTrivialAntiExceedanceEquiv {n : ℕ}
    (e π : Equiv.Perm (Fin n)) :
    Quotient (Equiv.Perm.SameCycle.setoid π) ≃
      {x : Fin n // zagTrivialAntiExceedance e π x} := by
  classical
  let pick : Fin n → {x : Fin n // zagTrivialAntiExceedance e π x} := fun x => by
    let m := e (zagCycleMinPos e π x)
    refine ⟨π.symm m, ?_⟩
    have hzx : π.SameCycle (π.symm m) x := by
      simpa [m] using zagCycleMinPos_mem e π x
    have hmin := zagCycleMinPos_eq_of_sameCycle e π hzx
    simp only [zagTrivialAntiExceedance, Equiv.apply_symm_apply]
    rw [hmin]
  have pick_eq (x y : Fin n) (hxy : π.SameCycle x y) : pick x = pick y := by
    apply Subtype.ext
    simp only [pick]
    rw [zagCycleMinPos_eq_of_sameCycle e π hxy]
  refine Equiv.ofBijective (Quotient.lift pick pick_eq) ?_
  constructor
  · intro a b hab
    refine Quotient.inductionOn₂ a b ?_ hab
    intro x y hxy
    apply Quotient.sound
    have hpred :
        π.symm (e (zagCycleMinPos e π x)) =
          π.symm (e (zagCycleMinPos e π y)) :=
      congrArg Subtype.val hxy
    have hmin : e (zagCycleMinPos e π x) = e (zagCycleMinPos e π y) :=
      π.symm.injective hpred
    exact (zagCycleMinPos_mem e π x).symm.trans
      ((hmin.sameCycle π).trans (zagCycleMinPos_mem e π y))
  · rintro ⟨x, hx⟩
    refine ⟨Quotient.mk _ x, ?_⟩
    apply Subtype.ext
    change π.symm (e (zagCycleMinPos e π x)) = x
    rw [← hx]
    exact π.symm_apply_apply x

def zagNontrivialAntiExceedanceEquiv {n : ℕ}
    (e π : Equiv.Perm (Fin n)) :
    {x : Fin n // zagNontrivialAntiExceedance e π x} ≃
      {x : {x : Fin n // ¬zagExceedance e π x} //
        ¬zagTrivialAntiExceedance e π x.1} where
  toFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  invFun x := ⟨x.1.1, x.1.2, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def zagTrivialAntiExceedanceEquiv {n : ℕ}
    (e π : Equiv.Perm (Fin n)) :
    {x : Fin n // zagTrivialAntiExceedance e π x} ≃
      {x : {x : Fin n // ¬zagExceedance e π x} //
        zagTrivialAntiExceedance e π x.1} where
  toFun x := ⟨⟨x.1, zagTrivialAntiExceedance_not_exceedance e π x.2⟩, x.2⟩
  invFun x := ⟨x.1.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end MetaMathlibExt
