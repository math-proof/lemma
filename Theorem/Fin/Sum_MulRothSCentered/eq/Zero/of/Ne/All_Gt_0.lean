module

public import Mathlib
public import Theorem.Fin.InvolutiveRothFlip
public import Theorem.Fin.RothCentered_RothFlip.eq.NegRothCentered.of.RothBox.All_Gt_0
public import Theorem.Fin.RothCentered_RothFlip.eq.RothCentered.of.RothBox.Ne

public section

open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothCentered_cross_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.Sum_MulRothSCentered.eq.Zero.of.Ne.All_Gt_0
  {m : ℕ}
  {r : Fin m → ℕ}
  {h k : Fin m}
-- given
  (hr : ∀ h, 0 < r h)
  (hhk : h ≠ k) :
-- imply
  ∑ j : RothBox r, rothCentered r j h * rothCentered r j k = 0 := by
-- proof
  let e : RothBox r ≃ RothBox r :=
    (InvolutiveRothFlip r h).toPerm (rothFlip r h)
  have hreindex := Equiv.sum_comp e
    (fun j : RothBox r ↦ rothCentered r j h * rothCentered r j k)
  have hkh : k ≠ h := Ne.symm hhk
  have hneg :
    (∑ j : RothBox r,
        rothCentered r (rothFlip r h j) h * rothCentered r (rothFlip r h j) k) =
      -(∑ j : RothBox r, rothCentered r j h * rothCentered r j k) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [RothCentered_RothFlip.eq.NegRothCentered.of.RothBox.All_Gt_0 hr,
      RothCentered_RothFlip.eq.RothCentered.of.RothBox.Ne hkh]
    ring
  change
    (∑ j : RothBox r,
        rothCentered r (rothFlip r h j) h * rothCentered r (rothFlip r h j) k) =
      ∑ j : RothBox r, rothCentered r j h * rothCentered r j k at hreindex
  rw [hneg] at hreindex
  linarith


-- created on 2026-10-21
