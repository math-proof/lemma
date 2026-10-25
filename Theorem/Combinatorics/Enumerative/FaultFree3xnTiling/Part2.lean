/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.FaultFree3xnTiling.Part3


namespace MetaMathlibExt

theorem ff3_dominoes_matching {n : ℕ} {T : Finset (Finset (TilingCell n))}
    (hT : IsSquareDominoTiling T) : ff3IsMatching (ff3Dominoes T) := by
  refine ⟨?_, ?_⟩
  · intro d hd
    simp only [ff3Dominoes, Finset.mem_filter] at hd
    obtain ⟨hdT, hcard⟩ := hd
    obtain hsingle | hdomino := hT.1 d hdT
    · omega
    · exact hdomino
  · intro d₁ hd₁ d₂ hd₂ hne
    simp only [ff3Dominoes, Finset.mem_filter] at hd₁ hd₂
    exact hT.2.1 d₁ hd₁.1 d₂ hd₂.1 hne

theorem ff3_dominoes_faultFree {n : ℕ} {T : Finset (Finset (TilingCell n))}
    (hvalid : ∀ d ∈ T, IsSquareOrDomino d) (hT : IsVerticalFaultFree T) :
    IsVerticalFaultFree (ff3Dominoes T) := by
  intro k hk
  obtain ⟨d, hd, x, hxd, y, hyd, hrow, hx, hy⟩ := hT k hk
  refine ⟨d, ?_, x, hxd, y, hyd, hrow, hx, hy⟩
  simp only [ff3Dominoes, Finset.mem_filter]
  refine ⟨hd, ?_⟩
  have hxy : x ≠ y := by
    intro h
    subst y
    omega
  have htwo : ({x, y} : Finset (TilingCell n)) ⊆ d := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hxd
    · exact hyd
  have hcardTwo : ({x, y} : Finset (TilingCell n)).card = 2 := by simp [hxy]
  have hcardLower : 2 ≤ d.card := by
    rw [← hcardTwo]
    exact Finset.card_le_card htwo
  obtain hsingle | hdomino := hvalid d hd
  · omega
  · exact hdomino.1

theorem ff3_complete_tiling {n : ℕ} {D : Finset (Finset (TilingCell n))}
    (hD : ff3IsMatching D) : IsSquareDominoTiling (ff3Complete D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    simp only [ff3Complete, Finset.mem_union] at hd
    rcases hd with hd | hd
    · exact Or.inr (hD.1 d hd)
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hd
      exact Or.inl (by simp)
  · intro d₁ hd₁ d₂ hd₂ hne
    simp only [ff3Complete, Finset.mem_union] at hd₁ hd₂
    rcases hd₁ with hd₁ | hd₁ <;> rcases hd₂ with hd₂ | hd₂
    · exact hD.2 d₁ hd₁ d₂ hd₂ hne
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd₂
      simp only [ff3Uncovered, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [Finset.disjoint_left]
      intro z hz hzx
      simp only [Finset.mem_singleton] at hzx
      subst z
      exact hx d₁ hd₁ hz
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd₁
      simp only [ff3Uncovered, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [Finset.disjoint_left]
      intro z hzx hz
      simp only [Finset.mem_singleton] at hzx
      subst z
      exact hx d₂ hd₂ hz
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hd₁
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hd₂
      rw [Finset.disjoint_left]
      intro z hzx hzy
      simp only [Finset.mem_singleton] at hzx hzy
      subst z
      subst y
      exact hne rfl
  · intro x
    by_cases hx : ∃ d ∈ D, x ∈ d
    · obtain ⟨d, hd, hxd⟩ := hx
      exact ⟨d, Finset.mem_union_left _ hd, hxd⟩
    · refine ⟨{x}, Finset.mem_union_right _ ?_, by simp⟩
      apply Finset.mem_image.mpr
      refine ⟨x, ?_, rfl⟩
      simp only [ff3Uncovered, Finset.mem_filter, Finset.mem_univ, true_and]
      intro d hd hxd
      exact hx ⟨d, hd, hxd⟩

theorem ff3_complete_faultFree {n : ℕ} {D : Finset (Finset (TilingCell n))}
    (hD : IsVerticalFaultFree D) : IsVerticalFaultFree (ff3Complete D) := by
  intro k hk
  obtain ⟨d, hd, rest⟩ := hD k hk
  exact ⟨d, Finset.mem_union_left _ hd, rest⟩

theorem ff3_dominoes_complete {n : ℕ} {D : Finset (Finset (TilingCell n))}
    (hD : ff3IsMatching D) : ff3Dominoes (ff3Complete D) = D := by
  ext d
  constructor
  · intro hd
    simp only [ff3Dominoes, Finset.mem_filter, ff3Complete, Finset.mem_union] at hd
    obtain ⟨hd | hd, hcard⟩ := hd
    · exact hd
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hd
      simp at hcard
  · intro hd
    simp only [ff3Dominoes, Finset.mem_filter, ff3Complete, Finset.mem_union]
    exact ⟨Or.inl hd, (hD.1 d hd).1⟩

theorem ff3_complete_dominoes {n : ℕ} {T : Finset (Finset (TilingCell n))}
    (hT : IsSquareDominoTiling T) : ff3Complete (ff3Dominoes T) = T := by
  ext d
  constructor
  · intro hd
    simp only [ff3Complete, Finset.mem_union] at hd
    rcases hd with hd | hd
    · exact (Finset.mem_filter.mp hd).1
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
      simp only [ff3Uncovered, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨e, heT, hxe⟩ := hT.2.2 x
      rcases (isSquareOrDomino_iff e).mp (hT.1 e heT) with hsingle | hpair
      · obtain ⟨y, rfl⟩ := hsingle
        simp only [Finset.mem_singleton] at hxe
        subst y
        exact heT
      · obtain ⟨y, z, hyz, _, rfl⟩ := hpair
        have heDomino : {y, z} ∈ ff3Dominoes T := by
          simp [ff3Dominoes, heT, hyz]
        exact (hx {y, z} heDomino hxe).elim
  · intro hd
    rcases (isSquareOrDomino_iff d).mp (hT.1 d hd) with hsingle | hpair
    · obtain ⟨x, rfl⟩ := hsingle
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨x, ?_, rfl⟩
      simp only [ff3Uncovered, Finset.mem_filter, Finset.mem_univ, true_and]
      intro e he hxe
      obtain ⟨heT, hecard⟩ := Finset.mem_filter.mp he
      have hne : ({x} : Finset (TilingCell n)) ≠ e := by
        intro h
        subst e
        simp at hecard
      exact Finset.disjoint_left.mp (hT.2.1 {x} hd e heT hne) (by simp) hxe
    · obtain ⟨x, y, hxy, _, rfl⟩ := hpair
      apply Finset.mem_union_left
      simp [ff3Dominoes, hd, hxy]

end MetaMathlibExt
