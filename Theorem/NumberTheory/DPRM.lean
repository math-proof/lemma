/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DPRM.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
module

public import Mathlib.Computability.RE
public import Mathlib.NumberTheory.Dioph
public import Mathlib.Computability.Primrec.Basic
public import Mathlib.Computability.Primrec.List
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.ChineseRemainder
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Int.GCD
public import Mathlib.Logic.Godel.GodelBetaFunction
public import Mathlib.Tactic
public import Def.NumberTheory.DPRM
open scoped Dioph Vector3 Nat Function

public section

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
