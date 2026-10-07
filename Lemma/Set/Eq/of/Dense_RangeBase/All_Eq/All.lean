import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
[AlgebraicGeometry_ext_of_isSeparated_of_dense_iUnion_range_of_comp_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_ext_of_isSeparated_of_dense_iUnion_range_of_comp_eq.lean)
-/
@[main]
private lemma main
  {X Y Z : Scheme.{u}} [IsReduced X]
  {f g : X ⟶ Y}
  {s : Y ⟶ Z} [IsSeparated s]
  {ι : Type u}
  {T : ι → Scheme.{u}}
-- given
  (hs : f ≫ s = g ≫ s)
  (z : ∀ i, T i ⟶ X)
  (hz : ∀ i, z i ≫ f = z i ≫ g)
  (hdense : Dense (⋃ i, Set.range (z i).base)) :
-- imply
  f = g := by
-- proof
  classical

  let c : (∐ T) ⟶ X := Sigma.desc z
  have : IsDominant c := by
    refine ⟨?_⟩
    apply Dense.mono ?_ hdense
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_range] at hx
    obtain ⟨i, t, rfl⟩ := hx
    refine ⟨(Sigma.ι T i).base t, ?_⟩
    show (Sigma.ι T i ≫ c).base t = (z i).base t
    rw [Sigma.ι_desc]
  refine ext_of_isDominant_of_isSeparated s hs c ?_
  apply Sigma.hom_ext
  intro i
  rw [Sigma.ι_desc_assoc, Sigma.ι_desc_assoc, hz]


-- created on 2026-10-05
