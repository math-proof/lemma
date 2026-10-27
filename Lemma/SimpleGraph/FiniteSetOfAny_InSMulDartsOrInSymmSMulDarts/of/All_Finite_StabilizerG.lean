import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.CerednikDrinfeld.SchottkyTreeAction
import Lemma.Int.P2MUtil

open CerednikDrinfeld.Mumford MulAction

/--
[CerednikDrinfeld_Mumford_finite_setOf_exists_mem_darts_smul_mem_darts](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CerednikDrinfeld_Mumford_finite_setOf_exists_mem_darts_smul_mem_darts.lean)
-/
@[path]
private lemma main
  [Group G] [MulAction G W]
  {𝒯 : SimpleGraph W} [GraphAction G 𝒯]
  {u v u' v' : W}
  {P : 𝒯.Walk u v}
  {Q : 𝒯.Walk u' v'}
-- given
  (hfin : ∀ w : W, Finite (stabilizer G w)) :
-- imply
  {γ : G | ∃ d ∈ Q.darts, γ • d ∈ P.darts ∨ (γ • d).symm ∈ P.darts}.Finite := by
-- proof
  classical
  have hcos : ∀ d d' : 𝒯.Dart, {γ : G | γ • d = d'}.Finite := by
    intro d d'
    by_cases h : ∃ γ₀ : G, γ₀ • d = d'
    ·
      obtain ⟨γ₀, h0⟩ := h
      have : Finite (stabilizer G d.fst) := hfin d.fst
      have hst : ((stabilizer G d : Subgroup G) : Set G).Finite :=
        (Set.toFinite ((stabilizer G d.fst : Subgroup G) : Set G)).subset (stabilizer_dart_le 𝒯 d)
      refine (hst.image (fun σ => γ₀ * σ)).subset ?_
      intro γ hγ
      refine ⟨γ₀⁻¹ * γ, ?_, by group⟩
      show γ₀⁻¹ * γ ∈ stabilizer G d
      rwa [mem_stabilizer_iff, mul_smul, inv_smul_eq_iff, h0]
    ·
      push Not at h
      convert Set.finite_empty
      ext γ
      simpa using h γ
  refine (Set.Finite.biUnion (Q.darts.toFinset.finite_toSet) fun d _ =>
    Set.Finite.biUnion ((P.darts ++ P.darts.map SimpleGraph.Dart.symm).toFinset.finite_toSet)
      fun d' _ => hcos d d').subset ?_
  rintro γ ⟨d, hd, hγ⟩
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, List.coe_toFinset, exists_prop]
  refine ⟨d, hd, ?_⟩
  rcases hγ with h1 | h2
  · exact ⟨γ • d, List.mem_append_left _ h1, rfl⟩
  ·
    refine ⟨γ • d, List.mem_append_right _ ?_, rfl⟩
    rw [List.mem_map]
    exact ⟨(γ • d).symm, h2, SimpleGraph.Dart.symm_symm _⟩


-- created on 2026-10-23
-- updated on 2026-10-26
