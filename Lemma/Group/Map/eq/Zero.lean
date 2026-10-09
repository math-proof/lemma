import Mathlib
import sympy.Basic

open CategoryTheory groupCohomology Rep

/--
[groupCohomology_H2res_comp_H2inf_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_groupCohomology_H2res_comp_H2inf_eq_zero.lean)
-/
@[path]
private lemma main
  {k G : Type u} [CommRing k] [Group G]
  {A : Rep k G}
  {S : Subgroup G} [S.Normal] :
-- imply
  groupCohomology.map (A :=
-- proof
  A.quotientToInvariants S) (B := A)
         (QuotientGroup.mk' S) (Rep.ofHom (A.ρ.quotientToInvariants_lift S)) 2 ≫
       groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) 2 = 0 := by
   ext x
   induction x using H2_induction_on with | h β =>
   change (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) 2).hom
     ((groupCohomology.map (QuotientGroup.mk' S) (Rep.ofHom (A.ρ.quotientToInvariants_lift S)) 2).hom
       (H2π _ β)) = 0
   rw [H2π_comp_map_apply, H2π_comp_map_apply, H2π_eq_zero_iff]

   refine ⟨fun _ => (↑(β (1, 1)) : A), funext fun p => ?_⟩
   obtain ⟨s, t⟩ := p
   rw [d₁₂_hom_apply]
   change A.ρ (s : G) (↑(β (1, 1))) - ↑(β (1, 1)) + ↑(β (1, 1))
     = (↑(β (((s : G) : G ⧸ S), ((t : G) : G ⧸ S))) : A)
   rw [show ((s : G) : G ⧸ S) = 1 from (QuotientGroup.eq_one_iff _).2 s.2,
     show ((t : G) : G ⧸ S) = 1 from (QuotientGroup.eq_one_iff _).2 t.2, sub_add_cancel]
   exact (β (1, 1)).2 s


-- created on 2026-10-05
