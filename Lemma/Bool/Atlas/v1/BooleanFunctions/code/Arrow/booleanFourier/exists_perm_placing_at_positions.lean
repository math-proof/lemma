import Mathlib
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Arrow.booleanFourier.not_prefersOver_of_lt
open BooleanFourier Bool


/--
[exists_perm_placing_at_positions](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Arrow.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  {a b c : Fin m}
-- given
  (hm : m ≥ 3)
  (hab : a ≠ b)
  (hbc : b ≠ c)
  (hac : a ≠ c) :
-- imply
  ∃ σ : Equiv.Perm (Fin m), σ a = ⟨0, by omega⟩ ∧ σ b = ⟨1, by omega⟩ ∧ σ c = ⟨2, by omega⟩ := by
-- proof
  have hm0 : 0 < m := lt_of_lt_of_le (by norm_num) hm
  let p0 : Fin m := ⟨0, hm0⟩
  let p1 : Fin m := ⟨1, by omega⟩
  let p2 : Fin m := ⟨2, by omega⟩
  let σ₁ := Equiv.swap a p0
  let b' := σ₁ b
  let σ₂ := Equiv.swap b' p1
  let c' := σ₂ (σ₁ c)
  let σ₃ := Equiv.swap c' p2
  have ha1 : σ₁ a = p0 := Equiv.swap_apply_left a p0
  have hb'_ne_p0 : b' ≠ p0 := by
    intro h
    exact hab (σ₁.injective (by simpa only [ha1] using h.symm))
  have hp1_ne_p0 : p1 ≠ p0 := by simp [p0, p1, Fin.ext_iff]
  have hσ₂_p0 : σ₂ p0 = p0 := Equiv.swap_apply_of_ne_of_ne hb'_ne_p0.symm hp1_ne_p0.symm
  have hσ₂_b' : σ₂ b' = p1 := Equiv.swap_apply_left b' p1
  have hc'_ne_p0 : c' ≠ p0 := by
    intro h
    exact hac (σ₁.injective (σ₂.injective (by simpa only [ha1, hσ₂_p0] using h.symm)))
  have hc'_ne_p1 : c' ≠ p1 := by
    intro h
    apply hbc
    apply σ₁.injective
    apply σ₂.injective
    change σ₂ b' = c'
    simpa only [hσ₂_b'] using h.symm
  have hp2_ne_p0 : p2 ≠ p0 := by simp [p0, p2, Fin.ext_iff]
  have hp2_ne_p1 : p2 ≠ p1 := by simp [p1, p2, Fin.ext_iff]
  have hσ₃_p0 : σ₃ p0 = p0 := Equiv.swap_apply_of_ne_of_ne hc'_ne_p0.symm hp2_ne_p0.symm
  have hσ₃_p1 : σ₃ p1 = p1 := Equiv.swap_apply_of_ne_of_ne hc'_ne_p1.symm hp2_ne_p1.symm
  refine ⟨σ₃ * σ₂ * σ₁, ?_, ?_, ?_⟩
  ·
    show σ₃ (σ₂ (σ₁ a)) = p0
    rw [ha1, hσ₂_p0, hσ₃_p0]
  ·
    show σ₃ (σ₂ (σ₁ b)) = p1
    change σ₃ (σ₂ b') = p1
    rw [hσ₂_b', hσ₃_p1]
  ·
    show σ₃ (σ₂ (σ₁ c)) = p2
    change σ₃ c' = p2
    exact Equiv.swap_apply_left c' p2


lemma BooleanFourier.exists_perm_placing_at_positions
  {m : ℕ}
  {a b c : Fin m}
-- given
  (hm : m ≥ 3)
  (hab : a ≠ b)
  (hbc : b ≠ c)
  (hac : a ≠ c) :
-- imply
  ∃ σ : Equiv.Perm (Fin m), σ a = ⟨0, by omega⟩ ∧ σ b = ⟨1, by omega⟩ ∧ σ c = ⟨2, by omega⟩ :=
-- proof
  main hm hab hbc hac


-- created on 2026-10-23
-- updated on 2026-11-24
