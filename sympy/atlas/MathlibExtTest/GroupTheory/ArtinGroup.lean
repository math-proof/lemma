/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/GroupTheory/ArtinGroup.lean -/


import sympy.atlas.GroupTheory.ArtinGroup
import Lemma.Nat.AlternatingWord0.eq.One


/-! ### Examples -/

/-- Ordinary case: the type `A₂` Coxeter matrix `!![1, 3; 3, 1]` on `Fin 2`. Its Artin group is the
braid group on `3` strands, `⟨a, b | a b a = b a b⟩`; the braid relation is `braid_relation`. -/
example :
    letI M : CoxeterMatrix (Fin 2) :=
      ⟨!![1, 3; 3, 1], by decide, by decide, by intro i j h; fin_cases i <;> fin_cases j <;> revert h <;> decide⟩
    CoxeterMatrix.alternatingWord (CoxeterMatrix.ArtinGroup.of M 0) (CoxeterMatrix.ArtinGroup.of M 1) 3 =
      CoxeterMatrix.alternatingWord (CoxeterMatrix.ArtinGroup.of M 1) (CoxeterMatrix.ArtinGroup.of M 0) 3 := by
  exact CoxeterMatrix.ArtinGroup.braid_relation _ (by decide) (by decide)

/-- Boundary case: with an empty index type there are no generators, so there are no relations and
the Artin group is trivial. -/
example (M : CoxeterMatrix PEmpty) : M.artinRelationsSet = ∅ := by
  ext r
  refine ⟨?_, ?_⟩
  · rintro ⟨i, -⟩
    exact i.elim
  · rintro ⟨⟩

/-- Infinite-entry case: a Coxeter matrix whose only off-diagonal entry is `0` (encoding `∞`)
imposes no braid relator at all, so the relation set is empty and the Artin group is the free
group on the generators. -/
example :
    letI M : CoxeterMatrix (Fin 2) := ⟨!![1, 0; 0, 1], by decide, by decide, by
      intro i j h; fin_cases i <;> fin_cases j <;> revert h <;> decide⟩
    M.artinRelationsSet = ∅ := by
  ext r
  refine ⟨?_, ?_⟩
  · rintro ⟨i, j, hij, hM, -⟩
    fin_cases i <;> fin_cases j <;> simp_all
  · rintro ⟨⟩
