import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
Graded Nakayama: if degree-zero vanishes and every homogeneous element is in the positive-degree span, the module is zero
(atlas graded_nakayama).

[graded_nakayama](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SyzygiesKoszul.lean)
-/
@[path]
private lemma main
  [Field k]
  [CommRing S]
  [Algebra k S]
  [AddCommGroup N]
  [Module S N]
  [Module k N]
  [IsScalarTower k S N]
  {𝒮 : ℕ → Submodule k S} [GradedAlgebra 𝒮]
  {𝒩 : ℕ → Submodule k N}
-- given
  (hinter : DirectSum.IsInternal 𝒩)
  (_ : ∀ (i j : ℕ) (s : S) (n : N), s ∈ 𝒮 j → n ∈ 𝒩 i → s • n ∈ 𝒩 (i + j))
  (hdeg0 : 𝒩 0 = ⊥)
  (hSN : ∀ (d : ℕ) (n : N), n ∈ 𝒩 d →
    n ∈ Submodule.span k (⋃ (j : ℕ) (_ : 0 < j) (i : ℕ) (_ : i + j = d),
      Set.image2 HSMul.hSMul (↑(𝒮 j) : Set S) (↑(𝒩 i) : Set N))) :
-- imply
  ∀ n : N, n = 0 := by
-- proof
  have hall : ∀ d, 𝒩 d = ⊥ := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      cases d with
      | zero => exact hdeg0
      | succ d =>
        rw [Submodule.eq_bot_iff]
        intro n hn
        have hmem := hSN (d + 1) n hn
        have hset_zero : (⋃ (j : ℕ) (_ : 0 < j) (i : ℕ) (_ : i + j = d + 1),
          Set.image2 HSMul.hSMul (↑(𝒮 j) : Set S) (↑(𝒩 i) : Set N)) ⊆ {(0 : N)} := by
          intro x hx
          simp only [Set.mem_iUnion, Set.mem_image2] at hx
          obtain ⟨j, hj, i, hij, s, hs, m, hm, rfl⟩ := hx
          have hi : i < d + 1 := by omega
          rw [ih i hi] at hm
          simp at hm
          simp [hm]
        have hspan_bot : Submodule.span k
          (⋃ (j : ℕ) (_ : 0 < j) (i : ℕ) (_ : i + j = d + 1),
            Set.image2 HSMul.hSMul (↑(𝒮 j) : Set S) (↑(𝒩 i) : Set N)) = ⊥ := by
          have : Submodule.span k ({(0 : N)} : Set N) = ⊥ :=
            Submodule.span_singleton_eq_bot.mpr rfl
          exact le_antisymm (this ▸ Submodule.span_mono hset_zero) bot_le
        rw [hspan_bot] at hmem
        exact (Submodule.mem_bot k).mp hmem
  intro n
  have hint := hinter
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hint
  have htop := hint.2
  have hbot : ⨆ i, 𝒩 i = ⊥ := by simp [hall]
  rw [hbot] at htop
  exact (Submodule.mem_bot k).mp (htop ▸ Submodule.mem_top)


-- created on 2026-10-24
