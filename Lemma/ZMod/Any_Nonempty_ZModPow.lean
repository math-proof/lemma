import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped DirectSum


namespace AbelianGroups

/--
[fundamental_theorem_finite_abelian_groups](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/AbelianGroups.lean)
-/
@[path]
lemma fundamental_theorem_finite_abelian_groups
  {G : Type*}
  [AddCommGroup G]
  [Finite G] :
-- imply
  ∃ (ι : Type) (_ : Fintype ι) (p : ι → ℕ) (_ : ∀ i, Nat.Prime (p i)) (e : ι → ℕ), Nonempty (G ≃+ ⨁ i : ι, ZMod (p i ^ e i)) :=
-- proof
  AddCommGroup.equiv_directSum_zmod_of_finite G

end AbelianGroups

namespace AbelianGroups

/--
[torsion_subgroup_structure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/AbelianGroups.lean)
-/
@[path]
lemma torsion_subgroup_structure
  {A : Type*}
  [AddCommGroup A]
  [AddGroup.FG A] :
-- imply
  ∃ (n : ℕ) (d : Fin n → ℕ) (_ : ∀ i, 0 < d i), Nonempty (AddCommGroup.torsion A ≃+ (⨁ i : Fin n, ZMod (d i))) := by
-- proof
  have hfg_tor : AddGroup.FG (AddCommGroup.torsion A) := by
    have : Module.Finite ℤ A := Module.Finite.iff_addGroup_fg.mpr ‹_›
    have hnoeth : IsNoetherian ℤ A := isNoetherian_of_isNoetherianRing_of_finite ℤ A
    have hfg_sub : (Submodule.torsion ℤ A).FG := IsNoetherian.noetherian _
    rw [AddGroup.fg_iff_addSubgroup_fg]
    rw [← Submodule.torsion_int]
    exact (Submodule.fg_iff_addSubgroup_fg _).mp hfg_sub
  have htor : AddMonoid.IsTorsion (AddCommGroup.torsion A) := by
    intro ⟨x, hx⟩
    rw [AddCommGroup.mem_torsion] at hx
    rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    obtain ⟨n, hn, hn'⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp hx
    exact ⟨n, hn, by ext; simp [hn']⟩
  have hfin : Finite (AddCommGroup.torsion A) :=
    @AddCommGroup.finite_of_fg_torsion _ _ hfg_tor htor
  obtain ⟨ι, hι, p, hp, e, ⟨f⟩⟩ :=
    AddCommGroup.equiv_directSum_zmod_of_finite (AddCommGroup.torsion A)
  let g : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun i => p (g.symm i) ^ e (g.symm i), fun i => ?_,
    ⟨f.trans (DirectSum.equivCongrLeft g)⟩⟩
  exact Nat.pos_of_ne_zero (pow_ne_zero _ (Nat.Prime.ne_zero (hp _)))

end AbelianGroups


-- created on 2026-10-23
