import Mathlib
import sympy.Basic
import Lemma.GroupCohomology.TateCohomology
import Lemma.GroupCohomology.TateSeam
import Lemma.Int.P2MUtil

open CategoryTheory Rep

/--
[Rep_exact_tateDeltaNeg1_tateH0Map](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Rep_exact_tateDeltaNeg1_tateH0Map.lean)
-/
@[path]
private lemma main
  {k : Type u} [CommRing k]
  {G : Type v} [Group G] [Fintype G]
  {X : ShortComplex (Rep.{w} k G)}
-- given
  (hX : X.ShortExact) :
-- imply
  Function.Exact (Rep.tateδneg1 hX) (Rep.tateH0Map X.f) := by
-- proof
  intro y
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [Rep.tateH0Map_mk, Submodule.Quotient.mk_eq_zero]
  constructor
  ·
    rintro ⟨β, hβ⟩
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ β
    have hb : X.f.hom a = X.X₂.ρ.norm b := (congrArg Subtype.val hβ).symm
    have hgb : X.X₃.ρ.norm (X.g.hom b) = 0 := by
      rw [← Rep.hom_norm_apply, ← hb, Rep.seam_g_f_apply]
    exact ⟨Rep.seamθ X ⟨b, hgb⟩, Rep.tateδneg1_mk hX b hgb a hb⟩
  ·
    rintro ⟨x, hx⟩
    obtain ⟨t, rfl⟩ := Rep.seamθ_surjective hX x
    have ht : Rep.tateδneg1 hX (Rep.seamθ X t) =
        Submodule.Quotient.mk ⟨Rep.seamψ hX t, Rep.seamψ_mem_invariants hX t⟩ :=
      Rep.tateδneg1_mk hX t.1 t.2 ⟨Rep.seamψ hX t, Rep.seamψ_mem_invariants hX t⟩ (Rep.f_seamψ hX t)
    rw [ht] at hx

    obtain ⟨γ, hγ⟩ := (Submodule.Quotient.eq _).1 hx.symm
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ γ

    refine ⟨Submodule.Quotient.mk (X.f.hom c + (t : X.X₂)), Subtype.ext ?_⟩
    have hγ' : X.X₁.ρ.norm c = (a : X.X₁) - Rep.seamψ hX t := congrArg Subtype.val hγ
    change X.X₂.ρ.norm (X.f.hom c + (t : X.X₂)) = X.f.hom a
    rw [map_add, ← Rep.hom_norm_apply, hγ', map_sub, Rep.f_seamψ, sub_add_cancel]


-- created on 2026-10-23
