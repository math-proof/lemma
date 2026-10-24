import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_GroupCohomology_TateCohomology
import Lemma.Definitions.Def_GroupCohomology_TateDimensionShift
import Lemma.Int.P2MUtil

open CategoryTheory Rep

/--
[Rep_indBotIota_apply](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Rep_indBotIota_apply.lean)
-/
@[path]
private lemma main
  {k G : Type u} [CommRing k] [Group G] [Fintype G]
  {A : Rep.{u} k G}
  {a : A} :
-- imply
  (Rep.indBotι A).hom a = ∑ g : G, A.indBotMk g (A.ρ g a) := by
-- proof
  classical
  unfold Rep.indBotι
  rw [Rep.resIndAdjunction_unit_app]
  change Rep.coindToInd _ (((Rep.resCoindAdjunction k _).unit.app A).hom a) = _
  rw [Rep.coindToInd_apply]

  have hbij : Function.Bijective (Quotient.mk'' : G → Quotient (QuotientGroup.rightRel (⊥ : Subgroup G))) :=
    ⟨fun x y h => by
      have hxy : QuotientGroup.rightRel (⊥ : Subgroup G) x y := Quotient.exact' h
      rw [QuotientGroup.rightRel_apply, Subgroup.mem_bot] at hxy
      exact (mul_inv_eq_one.1 hxy).symm,
     fun q => Quotient.inductionOn' q fun g => ⟨g, rfl⟩⟩
  refine (Finset.sum_bij (fun g _ => Quotient.mk'' g) (fun _ _ => by convert Finset.mem_univ _) (fun _ _ _ _ h => hbij.1 h)
    (fun q _ => (hbij.2 q).elim fun g hg => ⟨g, Finset.mem_univ _, hg⟩) (fun g _ => ?_)).symm

  rfl


-- created on 2026-10-23
