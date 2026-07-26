import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.Infinitesimal.is.InfiniteInv
import Lemma.Hyperreal.InfinitesimalSub.of.EqSt.Ne_0
import Lemma.Hyperreal.Ne_0.of.Infinite
import Lemma.Hyperreal.StDiv.eq.InvStInv
import Lemma.Nat.Add
import Lemma.Rat.Div.eq.DivDivS.of.Ne_0
import Lemma.Rat.Div.eq.One.of.Ne_0
import Lemma.Rat.Div1.eq.Inv
import Lemma.Rat.DivAdd.eq.AddDivS
import Lemma.Rat.Eq.is.EqInv
open Hyperreal Nat Rat


@[main, mp, mpr]
private lemma main
  {b y : ℝ*}
-- given
  (h_y : y → ∞)
  (h_by : b ≠ -y) :
-- imply
  stdPart (b / y) = -1 ↔ (y / (b + y)) → ∞ := by
-- proof
  constructor <;>
    intro h
  .
    have h_ε := InfinitesimalSub.of.EqSt.Ne_0 (by grind) h
    simp at h_ε
    have h_y0 := Ne_0.of.Infinite h_y
    have h_by : y / (b + y) = (b / y + 1)⁻¹ := by
      rw [Div.eq.DivDivS.of.Ne_0 h_y0]
      rw [DivAdd.eq.AddDivS]
      rw [Div.eq.One.of.Ne_0 h_y0]
      rw [Div1.eq.Inv]
    rw [h_by]
    have : NeZero (b / y + 1) := ⟨by grind⟩
    rwa [InfiniteInv.is.Infinitesimal]
  .
    apply Hyperreal.EqSt.of.InfinitesimalSub
    simp
    have h_b := Ne_0.of.Infinite h_y
    rw [Div.eq.DivDivS.of.Ne_0 h_b] at h
    rw [DivAdd.eq.AddDivS] at h
    rw [Div.eq.One.of.Ne_0 h_b] at h
    rw [Div1.eq.Inv] at h
    apply Infinitesimal.of.InfiniteInv h


@[main, mp, mpr]
private lemma left
  {b y : ℝ*}
-- given
  (h_b : b → ∞)
  (h_by : b ≠ -y) :
-- imply
  stdPart (b / y) = -1 ↔ (b / (b + y)) → ∞ := by
-- proof
  constructor <;>
    intro h
  .
    rw [StDiv.eq.InvStInv] at h
    have h := Eq.of.EqInv h
    simp at h
    have h_ε' := InfinitesimalSub.of.EqSt.Ne_0 (by grind) h
    simp at h_ε'
    have h_b0 := Ne_0.of.Infinite h_b
    have h_yb : b / (b + y) = (y / b + 1)⁻¹ := by
      rw [Div.eq.DivDivS.of.Ne_0 h_b0]
      rw [DivAdd.eq.AddDivS]
      rw [Div.eq.One.of.Ne_0 h_b0]
      rw [Add.comm]
      rw [Div1.eq.Inv]
    rw [h_yb]
    have : NeZero (y / b + 1) := ⟨by grind⟩
    rwa [InfiniteInv.is.Infinitesimal]
  .
    rw [StDiv.eq.InvStInv]
    apply EqInv.of.Eq
    simp
    apply EqSt.of.InfinitesimalSub
    simp
    rw [Add.comm]
    have h_b := Ne_0.of.Infinite h_b
    rw [Div.eq.DivDivS.of.Ne_0 h_b] at h
    rw [DivAdd.eq.AddDivS] at h
    rw [Div.eq.One.of.Ne_0 h_b] at h
    rw [Div1.eq.Inv] at h
    apply Infinitesimal.of.InfiniteInv h


-- created on 2026-07-26
