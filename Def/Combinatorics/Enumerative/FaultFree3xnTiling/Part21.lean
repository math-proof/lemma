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
import Theorem.Combinatorics.Enumerative.FaultFree3xnTiling.Part16


namespace MetaMathlibExt

def ff3CodeZeroFilling {a : Finset (Fin 3)} (c : ff3Code a 0) :
    ff3ColumnFilling a ∅ := by
  refine ⟨(c.2 0).1, ?_⟩
  simpa [ff3Incoming, ff3Outgoing] using (c.2 0).property

def ff3FillingCodeZero {a : Finset (Fin 3)} (f : ff3ColumnFilling a ∅) :
    ff3Code a 0 := by
  refine ⟨Fin.elim0, fun j ↦ ?_⟩
  refine ⟨f.1, ?_⟩
  have hj : j = 0 := Fin.eq_zero j
  subst j
  simpa [ff3Incoming, ff3Outgoing] using f.property

def ff3CodeZeroEquiv (a : Finset (Fin 3)) : ff3Code a 0 ≃ ff3Path a 0 where
  toFun := ff3CodeZeroFilling
  invFun := ff3FillingCodeZero
  left_inv c := by
    apply ff3_code_ext
    · funext j
      exact Fin.elim0 j
    · intro j
      have hj : j = 0 := Fin.eq_zero j
      subst j
      rfl
  right_inv f := Subtype.ext rfl

noncomputable def ff3CodePathEquiv :
    (a : Finset (Fin 3)) → (n : ℕ) → ff3Code a n ≃ ff3Path a n
  | a, 0 => ff3CodeZeroEquiv a
  | a, n + 1 =>
      { toFun := fun c ↦
          ⟨c.1 0, ff3CodeHeadFilling c,
            ff3CodePathEquiv (ff3ProfileRows (c.1 0)) n (ff3CodeTail c)⟩
        invFun := fun x ↦
          ff3CodeCons x.1 x.2.1
            ((ff3CodePathEquiv (ff3ProfileRows x.1) n).symm x.2.2)
        left_inv := fun c ↦ by
          change ff3CodeCons (c.1 0) (ff3CodeHeadFilling c)
            ((ff3CodePathEquiv (ff3ProfileRows (c.1 0)) n).symm
              (ff3CodePathEquiv (ff3ProfileRows (c.1 0)) n (ff3CodeTail c))) = c
          rw [Equiv.symm_apply_apply]
          exact ff3_codeCons_head_tail c
        right_inv := fun x ↦ by
          obtain ⟨p, f, t⟩ := x
          change (⟨p,
            (ff3CodeHeadFilling
                (ff3CodeCons p f ((ff3CodePathEquiv (ff3ProfileRows p) n).symm t)),
              ff3CodePathEquiv (ff3ProfileRows p) n
                (ff3CodeTail
                  (ff3CodeCons p f ((ff3CodePathEquiv (ff3ProfileRows p) n).symm t))))⟩ :
                  ff3Path a (n + 1)) = ⟨p, (f, t)⟩
          rw [ff3_codeHeadFilling_cons, ff3_codeTail_cons, Equiv.apply_symm_apply] }

/-- The actual number of vertical-fault-free square-and-domino tilings of a
`3 × n` rectangle. -/
noncomputable def verticalFaultFreeTilingCount (n : ℕ) : ℕ :=
  Nat.card {T : Finset (Finset (TilingCell n)) //
    IsSquareDominoTiling T ∧ IsVerticalFaultFree T}

/-- `tilingCount n` is the paper's recurrence-defined sequence `V_n`.
`tilingCount 0 = 0` is a dummy outside the paper's range `n ≥ 1`. -/
def tilingCount : ℕ → ℤ
  | 0 => 0
  | 1 => 3
  | 2 => 13
  | 3 => 26
  | 4 => 66
  | 5 => 154
  | 6 => 380
  | (n + 7) => tilingCount (n + 6) + 4 * tilingCount (n + 5)
      - tilingCount (n + 4) - tilingCount (n + 3)

def ff3ModelCount : ℕ → ℕ
  | 0 => 0
  | 1 => 3
  | n + 2 => ff3TransferCount ℕ n

noncomputable def ff3TilingPathEquiv (n : ℕ) :
    ff3FaultFreeTilings (n + 1) ≃ ff3Path ∅ n :=
  (ff3_tilingMatchingEquiv (n + 1)).trans <|
    (ff3_matchingEdgeEquiv n).symm.trans <|
      (ff3CodeEdgeEquiv n).symm.trans (ff3CodePathEquiv ∅ n)

end MetaMathlibExt
