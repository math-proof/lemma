import Mathlib
import Initialize.Tactic.Attr.Basic
open Module.End Module
open Submodule


private lemma exists_forall_apply_eq_smul_of_pairwise_commute'
  {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Nontrivial V]
  {ι : Type*} (T : ι → Module.End K V) (hT : Pairwise fun i j ↦ Commute (T i) (T j)) :
  ∃ v : V, v ≠ 0 ∧ ∀ i, ∃ c : K, T i v = c • v := by
  classical
  have hcomm : ∀ i j, Commute (T i) (T j) := by
    intro i j
    obtain rfl | h := eq_or_ne i j
    · exact Commute.refl _
    · exact hT h
  suffices key : ∀ n : ℕ, ∀ W : Submodule K V, finrank K W = n → W ≠ ⊥ →
      (∀ i, ∀ w ∈ W, T i w ∈ W) → ∃ v ∈ W, v ≠ 0 ∧ ∀ i, ∃ c : K, T i v = c • v by
    obtain ⟨v, -, hv0, hv⟩ := key _ ⊤ rfl (by simp) (fun i w _ => mem_top)
    exact ⟨v, hv0, hv⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W hWn hW0 hWinv
    if hscal : ∀ i, ∃ c : K, ∀ w ∈ W, T i w = c • w then
      obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
      refine ⟨v, hvW, hv0, fun i => ?_⟩
      obtain ⟨c, hc⟩ := hscal i
      exact ⟨c, hc v hvW⟩
    else
      push Not at hscal
      obtain ⟨i₀, hi₀⟩ := hscal
      have hmaps : ∀ w ∈ W, (T i₀) w ∈ W := hWinv i₀
      let S : Module.End K W := (T i₀).restrict hmaps
      have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW0
      obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue S
      let W' : Submodule K V := W ⊓ LinearMap.ker (T i₀ - μ • 1)
      have hW'le : W' ≤ W := inf_le_left
      have hmemW' : ∀ v, v ∈ W' ↔ v ∈ W ∧ T i₀ v = μ • v := by
        intro v
        simp only [W', mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
          Module.End.one_apply, sub_eq_zero]
      have hW'0 : W' ≠ ⊥ := by
        obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
        have hw0 : (w : V) ≠ 0 := fun h => hw.2 (Subtype.ext h)
        have hwapp : T i₀ (w : V) = μ • (w : V) := by
          have := hw.apply_eq_smul
          have h2 := congrArg Subtype.val this
          simpa [S, LinearMap.restrict_apply] using h2
        intro hbot
        have : (w : V) ∈ W' := (hmemW' _).mpr ⟨w.2, hwapp⟩
        rw [hbot, mem_bot] at this
        exact hw0 this
      have hW'ne : W' ≠ W := by
        intro hEq
        obtain ⟨w, hw, hne⟩ := hi₀ μ
        have : w ∈ W' := hEq ▸ hw
        exact hne ((hmemW' w).mp this).2
      have hlt : W' < W := lt_of_le_of_ne hW'le hW'ne
      have hdim : finrank K W' < n := hWn ▸ Submodule.finrank_lt_finrank_of_lt hlt
      have hW'inv : ∀ i, ∀ w ∈ W', T i w ∈ W' := by
        intro i w hw
        obtain ⟨hwW, hwT⟩ := (hmemW' w).mp hw
        refine (hmemW' _).mpr ⟨hWinv i w hwW, ?_⟩
        calc
          _ = T i (T i₀ w) := by
            have := hcomm i₀ i
            exact congrArg (fun f : Module.End K V => f w) this.eq
          _ = T i (μ • w) := by rw [hwT]
          _ = μ • T i w := by rw [LinearMap.map_smul]
      obtain ⟨v, hvW', hv0, hv⟩ := ih _ hdim W' rfl hW'0 hW'inv
      exact ⟨v, hW'le hvW', hv0, hv⟩

/--
[Module_End_exists_forall_apply_eq_smul_of_pairwise_commute](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_End_exists_forall_apply_eq_smul_of_pairwise_commute.lean)
-/
@[path]
private lemma main
  [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
  {T : ι → Module.End K V}
-- given
  (hT : Pairwise fun i j ↦ Commute (T i) (T j)) :
-- imply
  ∃ v : V, v ≠ 0 ∧ ∀ i, ∃ c : K, T i v = c • v := by
-- proof
  apply exists_forall_apply_eq_smul_of_pairwise_commute' T hT


-- created on 2026-10-24
