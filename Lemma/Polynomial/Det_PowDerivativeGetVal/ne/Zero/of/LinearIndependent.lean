import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Polynomial.Any_And_Det_PowDerivative.ne.Zero.of.LinearIndependent
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[roth_poly_wronskian_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {k : ℕ} [Field K] [CharZero K]
  (f : Fin k → K[X])
-- given
  (hf : LinearIndependent K f) :
-- imply
  (Matrix.det fun s j ↦ (derivative^[s.val]) (f j)) ≠ 0 := by
-- proof
  obtain ⟨n, hn, hdet⟩ := Any_And_Det_PowDerivative.ne.Zero.of.LinearIndependent f hf
  have hninj : Function.Injective n := by
    intro s t hst
    by_contra hne
    apply hdet
    apply Matrix.det_zero_of_row_eq hne
    ext j
    rw [hst]
  have hnid : ∀ s : Fin k, n s = s.val := by
    cases k with
    | zero =>
      intro s
      apply Fin.elim0 s
    | succ k =>
      have hprefix : ∀ s : Fin (k + 1), ∀ t : Fin (k + 1), t.val ≤ s.val → n t = t.val := by
        intro s
        induction s using Fin.induction with
        | zero =>
          intro t ht
          have htval : t.val = 0 := Nat.eq_zero_of_le_zero (by simpa using ht)
          have ht0 : t = 0 := Fin.eq_of_val_eq htval
          subst t
          apply Nat.eq_zero_of_le_zero (hn 0)
        | succ s ih =>
          intro t ht
          if hts : t = s.succ then
            subst t
            apply Nat.le_antisymm (hn s.succ)
            by_contra hnot
            have hlt : n s.succ < s.succ.val := Nat.lt_of_not_ge hnot
            let u : Fin (k + 1) := ⟨n s.succ, hlt.trans s.succ.isLt⟩
            have hu : u.val ≤ s.castSucc.val := by
              dsimp [u]
              simpa using Nat.le_pred_of_lt hlt
            have hnu := ih u hu
            have hcollision : n u = n s.succ := by simpa [u] using hnu
            have hus := hninj hcollision
            have := congrArg Fin.val hus
            simp [u] at this
            omega
          else
            apply ih t
            have hne : t.val ≠ s.succ.val := by
              intro heq
              apply hts
              apply Fin.eq_of_val_eq heq
            have hlt : t.val < s.succ.val := lt_of_le_of_ne ht hne
            simpa using Nat.le_pred_of_lt hlt
      intro s
      apply hprefix s s le_rfl
  simpa only [hnid] using hdet


-- created on 2026-10-21
