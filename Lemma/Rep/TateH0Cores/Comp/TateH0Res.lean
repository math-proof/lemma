import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.GroupCohomology.TateCohomology
import Def.GroupCohomology_TateResCor
import Lemma.Int.P2MUtil

open CategoryTheory Rep

/--
[Rep_tateH0Cores_comp_tateH0Res](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Rep_tateH0Cores_comp_tateH0Res.lean)
-/
@[path]
private lemma main
  {k : Type u} [CommRing k]
  {G : Type v} [Group G] [Fintype G]
  {S : Subgroup G} [Fintype S]
  {A : Rep.{w} k G} :
-- imply
  Rep.tateH0Cores S A ∘ₗ Rep.tateH0Res S A = (S.index : k) • LinearMap.id := by
-- proof
  letI := Fintype.ofFinite (G ⧸ S)
  refine Submodule.linearMap_qext _ (LinearMap.ext fun a => ?_)
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.smul_apply, LinearMap.id_apply,
    Rep.tateH0Res_mk]
  rw [← Submodule.Quotient.mk_smul]
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  rw [Representation.TateResCor.coe_cosetNormInvariants_apply, Submodule.coe_inclusion, Submodule.coe_smul,
    Representation.TateResCor.cosetNorm_apply, Finset.sum_congr rfl fun q _ => (Representation.mem_invariants _ _).1 a.2 q.out,
    Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, Nat.cast_smul_eq_nsmul]


-- created on 2026-10-23
