/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/TelescopicSequence.lean -/


import sympy.atlas.NumberTheory.TelescopicSequence
import Mathlib.Tactic

namespace MetaMathlibExt

example : telescopicGcd [660, 550, 352, 50, 201] 1 = 660 := by decide
example : telescopicC [660, 550, 352, 50, 201] 2 = 6 := by decide
example : telescopicC [660, 550, 352, 50, 201] 5 = 2 := by decide

example : IsTelescopic [4, 6, 5] := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro j hj hjlen
  have hjlen' : j ≤ 3 := by simpa using hjlen
  have hj_cases : j = 2 ∨ j = 3 := by omega
  rcases hj_cases with rfl | rfl
  · norm_num [telescopicC, telescopicGcd]
    have h4 : 4 ∈ AddSubmonoid.closure ({4} : Set ℕ) :=
      AddSubmonoid.subset_closure (by simp)
    simpa using add_mem (add_mem h4 h4) h4
  · norm_num [telescopicC, telescopicGcd]
    have h4 : 4 ∈ AddSubmonoid.closure {x : ℕ | x = 4 ∨ x = 6} :=
      AddSubmonoid.subset_closure (by simp)
    have h6 : 6 ∈ AddSubmonoid.closure {x : ℕ | x = 4 ∨ x = 6} :=
      AddSubmonoid.subset_closure (by simp)
    simpa using add_mem h4 h6

example : ¬ IsTelescopic [3, 4, 5] := by
  intro h
  have hmem := h.2.2 3 (by omega) (by norm_num)
  norm_num [telescopicC, telescopicGcd] at hmem
  have hshape : ∀ x : ℕ, x ∈ AddSubmonoid.closure {x : ℕ | x = 3 ∨ x = 4} →
      x = 0 ∨ x = 3 ∨ x = 4 ∨ 6 ≤ x := by
    intro x hx
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx => rcases hx with rfl | rfl <;> simp
    | zero => simp
    | add x y hx hy ihx ihy =>
      rcases ihx with rfl | rfl | rfl | hx6 <;>
        rcases ihy with rfl | rfl | rfl | hy6 <;> simp_all <;> omega
  have := hshape 5 hmem
  omega

end MetaMathlibExt
