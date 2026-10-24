import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.Words


namespace CoxeterSystem

/--
[mem_alternatingWord](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ParabolicDecomp.lean)
-/
@[path]
private lemma mem_alternatingWord
  [DecidableEq B]
  [Group W]
  {M : CoxeterMatrix B}
  {_ : CoxeterSystem M W}
  {i j : B}
  {m : ℕ}
  {b : B}
-- given
  (hb : b ∈ alternatingWord i j m) :
-- imply
  b = i ∨ b = j := by
-- proof
  induction m generalizing i j with
  | zero =>
    simp [show alternatingWord i j 0 = [] from rfl] at hb
  | succ n ih =>
    rw [alternatingWord_succ] at hb
    rw [List.concat_eq_append] at hb
    simp only [List.mem_append, List.mem_singleton] at hb
    obtain hb | hb := hb
    · exact (ih (i := j) (j := i) hb).symm
    · exact Or.inr hb

end CoxeterSystem

namespace CoxeterSystem

/--
[parabolic_decomp_rank2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ParabolicDecomp.lean)
-/
@[path]
private lemma parabolic_decomp_rank2
  [DecidableEq B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {w : W}
  {s t : B}
-- given
  (_ : s ≠ t) :
-- imply
  ∃ (x : W) (y_word : List B), x * cs.wordProd y_word = w ∧ cs.length (x * cs.simple s) = cs.length x + 1 ∧ cs.length (x * cs.simple t) = cs.length x + 1 ∧ (∀ b ∈ y_word, b = s ∨ b = t) ∧ cs.length x + y_word.length = cs.length w := by
-- proof
  induction h : cs.length w using Nat.strongRecOn generalizing w with
  | _ n ih =>
    obtain hasc_s | hdesc_s := cs.length_mul_simple w s
    ·
      obtain hasc_t | hdesc_t := cs.length_mul_simple w t
      ·
        exact ⟨w, [], by simp [cs.wordProd_nil], hasc_s, hasc_t,
          fun b hb => absurd hb List.not_mem_nil, by simp [h]⟩
      ·
        have hlt : cs.length (w * cs.simple t) < n := by omega
        obtain ⟨x, y_word, hprod, hxs, hxt, hmem, hlen_eq⟩ :=
          ih (cs.length (w * cs.simple t)) hlt (w := w * cs.simple t) rfl
        refine ⟨x, y_word ++ [t], ?_, hxs, hxt, ?_, ?_⟩
        ·
          rw [cs.wordProd_append, cs.wordProd_singleton, ← mul_assoc, hprod,
            mul_assoc, cs.simple_mul_simple_self, mul_one]
        ·
          intro b hb
          simp only [List.mem_append, List.mem_singleton] at hb
          exact hb.elim (hmem b) (fun h => Or.inr h)
        ·
          simp only [List.length_append, List.length_singleton]; omega
    ·
      have hlt : cs.length (w * cs.simple s) < n := by omega
      obtain ⟨x, y_word, hprod, hxs, hxt, hmem, hlen_eq⟩ :=
        ih (cs.length (w * cs.simple s)) hlt (w := w * cs.simple s) rfl
      refine ⟨x, y_word ++ [s], ?_, hxs, hxt, ?_, ?_⟩
      ·
        rw [cs.wordProd_append, cs.wordProd_singleton, ← mul_assoc, hprod,
          mul_assoc, cs.simple_mul_simple_self, mul_one]
      ·
        intro b hb
        simp only [List.mem_append, List.mem_singleton] at hb
        exact hb.elim (hmem b) (fun h => Or.inl h)
      ·
        simp only [List.length_append, List.length_singleton]; omega

end CoxeterSystem


-- created on 2026-10-24
