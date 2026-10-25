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
import Def.Combinatorics.Enumerative.FaultFree3xnTiling.Part18


namespace MetaMathlibExt

theorem ff3_profileRows_injective : Function.Injective ff3ProfileRows := by
  intro p q h
  exact ff3_profileRows_bijective.1 (Subtype.ext h)

theorem ff3_code_ext {a : Finset (Fin 3)} {n : ℕ} {c d : ff3Code a n}
    (hp : c.1 = d.1) (hv : ∀ j, (c.2 j).1 = (d.2 j).1) : c = d := by
  obtain ⟨p, f⟩ := c
  obtain ⟨q, g⟩ := d
  dsimp at hp hv
  subst q
  have hfg : f = g := by
    funext j
    exact Subtype.ext (hv j)
  subst g
  rfl

theorem ff3_codeEdges_edgeCode {n : ℕ} (E : ff3FaultFreeEdgeMatchings n) :
    ff3CodeEdges (ff3EdgeCode E) = E.1 := by
  ext e
  rcases e with e | e
  · rw [ff3_mem_codeEdges_horizontal]
    change e.1 ∈ ff3ProfileRows (ff3EdgeProfile E e.2) ↔ Sum.inl e ∈ E.1
    exact ff3_mem_edgeProfile E e.1 e.2
  · rw [ff3_mem_codeEdges_vertical]
    change ff3EdgeVertical E e.2 = some e.1 ↔ _
    exact ff3_edgeVertical_eq_some_iff E e.1 e.2

theorem ff3_edgeCode_codeEdges {n : ℕ} (c : ff3Code ∅ n) :
    ff3EdgeCode ⟨ff3CodeEdges c, ff3_codeEdges_isMatching c, ff3_codeEdges_crosses c⟩ = c := by
  let E : ff3FaultFreeEdgeMatchings n :=
    ⟨ff3CodeEdges c, ff3_codeEdges_isMatching c, ff3_codeEdges_crosses c⟩
  apply ff3_code_ext
  · funext k
    apply ff3_profileRows_injective
    ext r
    change r ∈ ff3ProfileRows (ff3EdgeProfile E k) ↔ r ∈ ff3ProfileRows (c.1 k)
    rw [ff3_mem_edgeProfile]
    exact ff3_mem_codeEdges_horizontal c r k
  · intro j
    change ff3EdgeVertical E j = (c.2 j).1
    cases hv : (c.2 j).1 with
    | none =>
        cases he : ff3EdgeVertical E j with
        | none => rfl
        | some r =>
            have hrE : Sum.inr (r, j) ∈ E.1 :=
              (ff3_edgeVertical_eq_some_iff E r j).mp he
            have hrc : (c.2 j).1 = some r :=
              (ff3_mem_codeEdges_vertical c r j).mp hrE
            rw [hv] at hrc
            contradiction
    | some r =>
        apply (ff3_edgeVertical_eq_some_iff E r j).mpr
        exact (ff3_mem_codeEdges_vertical c r j).mpr hv

end MetaMathlibExt
