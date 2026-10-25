/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/

import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Finite
import Instance.Combinatorics.Enumerative.ParkingFunction
import Lemma.Finset.Enumerative.ParkingFunction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.PollakPartialParkingFunctions.Part10


namespace MetaMathlibExt.PollakPartialParking

/-- Translation of circle preferences. -/
def transPerm (s t : ℕ) (c : ZMod (t + 1)) :
    (Fin s → ZMod (t + 1)) ≃ (Fin s → ZMod (t + 1)) :=
  { toFun := fun g i => g i + c,
    invFun := fun g i => g i - c,
    left_inv := by
      intro g
      funext i
      change (g i + c) - c = g i
      abel,
    right_inv := by
      intro g
      funext i
      change (g i - c) + c = g i
      abel }

/-- All fibers over circle spots have the same cardinality. -/
def fiberEquiv (s t : ℕ) (hst : s ≤ t) (x : ZMod (t + 1)) :
    {g : Fin s → ZMod (t + 1) // x ∈ parkEmpty s t g hst} ≃
    {g : Fin s → ZMod (t + 1) // extra t ∈ parkEmpty s t g hst} :=
  (transPerm s t (extra t - x)).subtypeEquiv (by
    intro g
    change (x ∈ parkEmpty s t g hst) ↔
      (extra t ∈ parkEmpty s t (fun i => g i + (extra t - x)) hst)
    constructor
    · intro h
      have himg := parkEmpty_translate s t g hst (extra t - x)
      have hx : x + (extra t - x) = extra t := by abel
      rw [himg]
      exact Finset.mem_image.mpr ⟨x, h, hx⟩
    · intro h
      have hfun : (fun i => (g i + (extra t - x)) + (-(extra t - x))) = g := by
        funext i
        abel
      have himg2 := parkEmpty_translate s t (fun i => g i + (extra t - x)) hst
        (-(extra t - x))
      rw [hfun] at himg2
      rw [himg2]
      have hx : extra t + (-(extra t - x)) = x := by abel
      exact Finset.mem_image.mpr ⟨extra t, h, hx⟩)

/-- Pairs as a sigma type. -/
def StoSigma (s t : ℕ) (hst : s ≤ t) :
    {p : (Fin s → ZMod (t + 1)) × ZMod (t + 1) //
      p.2 ∈ parkEmpty s t p.1 hst} ≃
    Σ _g : (Fin s → ZMod (t + 1)), ↥(parkEmpty s t _g hst) :=
  { toFun := fun ⟨⟨g, x⟩, h⟩ => ⟨g, ⟨x, h⟩⟩,
    invFun := fun ⟨g, ⟨x, h⟩⟩ => ⟨⟨g, x⟩, h⟩,
    left_inv := fun ⟨⟨_g, _x⟩, _h⟩ => rfl,
    right_inv := fun ⟨_g, ⟨_x, _h⟩⟩ => rfl }

/-- Fibers as a sigma type. -/
def TtoSigma (s t : ℕ) (hst : s ≤ t) :
    {p : ZMod (t + 1) × (Fin s → ZMod (t + 1)) //
      p.1 ∈ parkEmpty s t p.2 hst} ≃
    Σ _x : ZMod (t + 1), {g : Fin s → ZMod (t + 1) //
      _x ∈ parkEmpty s t g hst} :=
  { toFun := fun ⟨⟨x, g⟩, h⟩ => ⟨x, ⟨g, h⟩⟩,
    invFun := fun ⟨x, ⟨g, h⟩⟩ => ⟨⟨x, g⟩, h⟩,
    left_inv := fun ⟨⟨_x, _g⟩, _h⟩ => rfl,
    right_inv := fun ⟨_x, ⟨_g, _h⟩⟩ => rfl }

/-- Restricting a circle function avoiding the extra spot to linear spots. -/
def restrict (s t : ℕ) (g : Fin s → ZMod (t + 1))
    (h : ∀ i, g i ≠ extra t) : Fin s → Fin t :=
  fun i => ⟨(g i).val, by
    have : NeZero (t + 1) := ⟨by omega⟩
    have hlt := ZMod.val_lt (g i)
    by_contra hcon
    have heq : (g i).val = t := by omega
    apply h i
    have h1 : (((g i).val : ℕ) : ZMod (t + 1)) = g i := by
      have h2 := ZMod.natCast_val (R := ZMod (t + 1)) (g i)
      rwa [ZMod.cast_id] at h2
    rw [heq] at h1
    exact h1.symm⟩

end MetaMathlibExt.PollakPartialParking
