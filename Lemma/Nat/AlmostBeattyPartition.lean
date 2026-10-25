import Mathlib
import sympy.Basic
import Def.NumberTheory.AlmostBeattyPartition
open MetaMathlibExt


namespace MetaMathlibExt

/--
[beattyTerm_eq_floor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/AlmostBeattyPartition.lean)
-/
@[path]
lemma beattyTerm_eq_floor
  {n : { n : ℕ // 0 < n }}
  {α : ℝ} :
-- imply
  beattyTerm n α = Nat.floor ((n.val : ℝ) / α) := by
-- proof
  simp [beattyTerm, beattySeq, div_eq_mul_inv, Int.floor_toNat]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[beattyTerm_isAlmostBeattySequence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/AlmostBeattyPartition.lean)
-/
@[path]
lemma beattyTerm_isAlmostBeattySequence
  {α : ℝ}
-- given
  (hα0 : 0 < α)
  (hα1 : α < 1) :
-- imply
  IsAlmostBeattySequence (fun n => beattyTerm n α) α := by
-- proof
  have h1div : (1 : ℝ) < 1 / α := by
    have h10 : (1 : ℝ) * α < 1 := by
      simpa using hα1
    exact (lt_div_iff₀ hα0).mpr h10
  have hmono : StrictMono (fun n : { n : ℕ // 0 < n } => beattyTerm n α) := by
    intro m n hmn
    have hmn' : m.val < n.val := hmn
    have hmn1 : m.val + 1 ≤ n.val := by omega
    have hcast1 : (m.val : ℝ) + 1 ≤ (n.val : ℝ) := by
      have h : ((m.val + 1 : ℕ) : ℝ) ≤ ((n.val : ℕ) : ℝ) := Nat.cast_le.mpr hmn1
      rwa [Nat.cast_add, Nat.cast_one] at h
    have hA : ((m.val : ℝ) + 1) / α ≤ (n.val : ℝ) / α :=
      (div_le_div_iff_of_pos_right hα0).mpr hcast1
    rw [add_div] at hA
    have hB : (((m.val : ℝ) / α + 1 : ℝ)) < (((m.val : ℝ) / α + 1 / α : ℝ)) :=
      add_lt_add_right h1div (((m.val : ℝ) / α : ℝ))
    have key : (m.val : ℝ) / α + 1 < (n.val : ℝ) / α :=
      lt_of_lt_of_le hB hA
    have hx0 : (0 : ℝ) ≤ (m.val : ℝ) / α :=
      le_of_lt (div_pos (Nat.cast_pos.mpr m.2) hα0)
    have hxa : ((Nat.floor ((m.val : ℝ) / α) : ℕ) : ℝ) ≤ (m.val : ℝ) / α :=
      Nat.floor_le hx0
    have h1 : ((Nat.floor ((m.val : ℝ) / α) : ℕ) : ℝ) + 1 ≤ (m.val : ℝ) / α + 1 :=
      add_le_add_left hxa 1
    have h3 : (n.val : ℝ) / α < ((Nat.floor ((n.val : ℝ) / α) : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have h4 : ((Nat.floor ((m.val : ℝ) / α) : ℕ) : ℝ) + 1 <
      ((Nat.floor ((n.val : ℝ) / α) : ℕ) : ℝ) + 1 :=
      lt_trans (lt_of_le_of_lt h1 key) h3
    have h5 : ((Nat.floor ((m.val : ℝ) / α) : ℕ) : ℝ) <
      ((Nat.floor ((n.val : ℝ) / α) : ℕ) : ℝ) :=
      (add_lt_add_iff_right (1 : ℝ)).mp h4
    change beattyTerm m α < beattyTerm n α
    rw [beattyTerm_eq_floor, beattyTerm_eq_floor]
    exact Nat.cast_lt.mp h5
  have hpos : ∀ n : { n : ℕ // 0 < n }, 0 < beattyTerm n α := by
    intro n
    have hn1 : 1 ≤ n.val := n.2
    have hcastn : (1 : ℝ) ≤ (n.val : ℝ) := by
      have h : ((1 : ℕ) : ℝ) ≤ ((n.val : ℕ) : ℝ) := Nat.cast_le.mpr hn1
      rwa [Nat.cast_one] at h
    have hle : (1 : ℝ) ≤ (n.val : ℝ) / α := by
      rw [le_div_iff₀ hα0, one_mul]
      exact le_trans (le_of_lt hα1) hcastn
    have h2 : (1 : ℝ) < ((Nat.floor ((n.val : ℝ) / α) : ℕ) : ℝ) + 1 :=
      lt_of_le_of_lt hle (Nat.lt_floor_add_one _)
    have h3 : (0 : ℝ) + 1 < ((Nat.floor ((n.val : ℝ) / α) : ℕ) : ℝ) + 1 := by
      rwa [zero_add]
    have h4 : (0 : ℝ) < ((Nat.floor ((n.val : ℝ) / α) : ℕ) : ℝ) :=
      (add_lt_add_iff_right (1 : ℝ)).mp h3
    rw [beattyTerm_eq_floor]
    exact Nat.cast_pos.mp h4
  refine ⟨hα0, hα1, hmono, hpos, 0, fun n => by simp⟩

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
