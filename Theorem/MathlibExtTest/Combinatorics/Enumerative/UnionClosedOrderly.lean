/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/UnionClosedOrderly.lean -/


import Def.Combinatorics.Enumerative.UnionClosedOrderly
import Lemma.Finset.Enumerative.UnionClosedOrderly


namespace MetaMathlibExt

example : binRep 3 ({0, 2} : Finset (Fin 3)) = 5 := by
  decide

example : setKey 3 ({0, 2} : Finset (Fin 3)) = 13 := by
  decide

example : setLT 3 ({0, 1} : Finset (Fin 3)) {2} := by
  rw [setLT_iff_setKey_lt]
  decide

example : IsCanonical 1 ({∅} : Finset (Finset (Fin 1))) := by
  let A : Fin 1 → Finset (Fin 1) := fun _ => {0}
  have h :=
    orderly_canonical_prefix_of_sorted 1 1 0
      (insert ∅ (Finset.image A Finset.univ)) A
      (by decide) rfl (by simp [A])
      (by
        intro i j hij
        omega)
      (by
        intro σ
        have hσ : σ = Equiv.refl _ := Subsingleton.elim _ _
        subst σ
        rfl)
  simpa using h

example :
    let A : Fin 3 → Finset (Fin 2) := fun i =>
      if i = 0 then Finset.univ else if i = 1 then {0} else {1}
    IsCanonical 2
      (insert ∅ (Finset.image (fun i : Fin 2 => A (Fin.castLE (by decide) i)) Finset.univ)) := by
  dsimp only
  refine orderly_canonical_prefix 2 3 2
    (insert ∅ (insert Finset.univ
      (Finset.image (fun i : Fin 2 => ({i} : Finset (Fin 2))) Finset.univ)))
    (fun i => if i = 0 then Finset.univ else if i = 1 then {0} else {1})
    (by decide) (by decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · unfold setLT
    decide
  · decide
  · decide
  · unfold IsUnionClosed
    decide
  · intro σ
    have hperm :
        permImage 2 σ
          (insert ∅ (insert Finset.univ
            (Finset.image (fun i : Fin 2 => ({i} : Finset (Fin 2))) Finset.univ))) =
          insert ∅ (insert Finset.univ
            (Finset.image (fun i : Fin 2 => ({i} : Finset (Fin 2))) Finset.univ)) := by
      ext S
      suffices h :
          S = ∅ ∨ S = Finset.univ ∨ {σ 0} = S ∨ {σ 1} = S ↔
            S = ∅ ∨ S = Finset.univ ∨ {0} = S ∨ {1} = S by
        simpa [permImage] using h
      by_cases hσ0 : σ 0 = 0
      · have hσ1ne : σ 1 ≠ 0 := by
          intro hσ1
          exact (by decide : (1 : Fin 2) ≠ 0) (σ.injective (hσ1.trans hσ0.symm))
        rw [hσ0, Fin.eq_one_of_ne_zero (σ 1) hσ1ne]
      · have hσ0one : σ 0 = 1 := Fin.eq_one_of_ne_zero (σ 0) hσ0
        have hσ1 : σ 1 = 0 := by
          by_contra hσ1ne
          have hσ1one : σ 1 = 1 := Fin.eq_one_of_ne_zero (σ 1) hσ1ne
          exact (by decide : (1 : Fin 2) ≠ 0)
            (σ.injective (hσ1one.trans hσ0one.symm))
        simp only [hσ0one, hσ1, or_comm]
    rw [hperm]

end MetaMathlibExt
