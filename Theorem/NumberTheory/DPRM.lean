/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DPRM.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Computability.RE
import Mathlib.NumberTheory.Dioph
import Mathlib.Computability.Primrec.Basic
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Logic.Godel.GodelBetaFunction
import Mathlib.Tactic
import Def.NumberTheory.DPRM
open scoped Dioph Vector3 Nat Function


namespace MathlibExt.NumberTheory.DPRMWanted

/-- Backward direction: a β-coded sequence runs inside the recursion. -/
theorem dp_prec_bwd (f g : ℕ →. ℕ) (a c : ℕ)
    (h0 : Nat.beta c 0 ∈ f a) :
    ∀ (k : ℕ),
      (∀ j, j < k →
        Nat.beta c (j + 1) ∈ g (Nat.pair a (Nat.pair j (Nat.beta c j)))) →
      Nat.beta c k ∈ Nat.rec (motive := fun _ => Part ℕ) (f a)
        (fun j (IH : Part ℕ) => do
          let i ← IH; g (Nat.pair a (Nat.pair j i))) k := by
  intro k
  induction k with
  | zero =>
    intro _
    exact h0
  | succ k ih =>
    intro hall
    exact Part.mem_bind_iff.mpr
      ⟨Nat.beta c k, ih (fun j hj => hall j (by omega)),
        hall k (Nat.lt_succ_self k)⟩

end MathlibExt.NumberTheory.DPRMWanted
