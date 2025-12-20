import Lemma.Hyperreal.EqSt_0.of.Infinite
import Lemma.Hyperreal.EqSt_0.of.Infinitesimal
import Lemma.Hyperreal.GeStInv_0.of.NotInfinitesimal.StDiv.eq.One
import Lemma.Hyperreal.Infinite.is.InfiniteAdd
import Lemma.Hyperreal.Infinite.is.InfiniteAdd.of.NotInfinite
import Lemma.Hyperreal.Infinite.is.InfinitePow
import Lemma.Hyperreal.Infinitesimal.of.Infinitesimal.StDiv.ne.Zero
import Lemma.Hyperreal.Ne_0.Ne_0.of.NotInfinitesimal.StDiv.eq.One
import Lemma.Hyperreal.NotInfinite.of.Infinitesimal
import Lemma.Hyperreal.NotInfiniteInvMul.of.NotInfinitesimal.StDiv.eq.One
import Lemma.Hyperreal.NotInfiniteMul.of.NotInfinite
import Lemma.Hyperreal.NotInfiniteMul.of.NotInfinite.NotInfinite
import Lemma.Hyperreal.StAdd.eq.AddSt.of.NotInfinite
import Lemma.Hyperreal.StAdd.eq.AddStS.of.NotInfinite.NotInfinite
import Lemma.Hyperreal.StAdd.eq.Add_St.of.NotInfinite
import Lemma.Hyperreal.StDiv.eq.DivStS.of.NotInfinite.NotInfinitesimal
import Lemma.Hyperreal.StDiv.eq.Inv.of.EqSt
import Lemma.Hyperreal.StMul.eq.MulStS.of.NotInfinite.NotInfinite
import Lemma.Hyperreal.StMul.eq.Mul_St.of.NotInfinite
import Lemma.Hyperreal.StPow.eq.PowSt.of.NotInfinite
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.Mul.ne.Zero.of.Ne_0.Ne_0
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Nat.Ne_0.of.Eq
import Lemma.Rat.Div.eq.One.of.Ne_0
import Lemma.Rat.Div_Add_Square.eq.Div_AddInvMul.of.Ne_0.Ne_0
open Hyperreal Nat Rat


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h : st (a / b) = 1) :
-- imply
  ((1 + 2 * a * b) / (1 + a² + b²)).st = 1 := by
-- proof
  if h_a : a.Infinitesimal then
    have h_b := Infinitesimal.of.Infinitesimal.StDiv.ne.Zero.left (by linarith) h_a (b := b)
    have h_a₀ := EqSt_0.of.Infinitesimal h_a
    have h_b₀ := EqSt_0.of.Infinitesimal h_b
    have h_a' := NotInfinite.of.Infinitesimal h_a
    have h_b' := NotInfinite.of.Infinitesimal h_b
    have h_a₂ := StPow.eq.PowSt.of.NotInfinite h_a' (n := 2)
    have h_b₂ := StPow.eq.PowSt.of.NotInfinite h_b' (n := 2)
    simp [h_a₀] at h_a₂
    simp [h_b₀] at h_b₂
    have h_ab := StMul.eq.MulStS.of.NotInfinite.NotInfinite h_a' h_b'
    simp [h_a₀, h_b₀] at h_ab
    have h_ab' := NotInfiniteMul.of.NotInfinite.NotInfinite h_a' h_b'
    have h_2ab := StMul.eq.Mul_St.of.NotInfinite 2 h_ab'
    have h_2ab' := NotInfiniteMul.of.NotInfinite.left 2 h_ab'
    have h_1_2ab := StAdd.eq.Add_St.of.NotInfinite 1 h_2ab'
    rw [h_2ab, Mul_Mul.eq.MulMul, h_ab] at h_1_2ab
    simp at h_1_2ab
    have h_a₂' := NotInfinitePow.of.NotInfinite h_a' (n := 2)
    have h_b₂' := NotInfinitePow.of.NotInfinite h_b' (n := 2)
    have h_ab' := StAdd.eq.AddStS.of.NotInfinite.NotInfinite h_a₂' h_b₂'
    simp [h_a₂, h_b₂] at h_ab'
    have h_a₂b₂' := NotInfiniteAdd.of.NotInfinite.NotInfinite h_a₂' h_b₂'
    have h_1_a₂b₂ := StAdd.eq.Add_St.of.NotInfinite 1 h_a₂b₂'
    simp [h_ab', Add_Add.eq.AddAdd] at h_1_a₂b₂
    have h_1_2ab' := Ne_0.of.Eq h_1_2ab
    have h_1_2ab' := NotInfinite.of.NeSt_0 h_1_2ab'
    have h_1_a₂b₂' := Ne_0.of.Eq h_1_a₂b₂
    have h_1_a₂b₂' := NotInfinitesimal.of.NeSt_0 h_1_a₂b₂'
    have h_div := StDiv.eq.DivStS.of.NotInfinite.NotInfinitesimal h_1_2ab' h_1_a₂b₂'
    simp [h_1_a₂b₂, h_1_2ab] at h_div
    assumption
  else
    have h_nonneg_st_inv_ab := GeStInv_0.of.NotInfinitesimal.StDiv.eq.One h h_a
    have h_ne_inf_inv_ab := NotInfiniteInvMul.of.NotInfinitesimal.StDiv.eq.One h h_a
    let ⟨h_a_ne_0, h_b_ne_0⟩ := Ne_0.Ne_0.of.NotInfinitesimal.StDiv.eq.One h h_a
    rw [Div_Add_Square.eq.Div_AddInvMul.of.Ne_0.Ne_0 h_a_ne_0 h_b_ne_0]
    have h_2_ab_st := StAdd.eq.AddSt.of.NotInfinite h_ne_inf_inv_ab 2
    have h_div_ba := StDiv.eq.Inv.of.EqSt h
    simp at h_div_ba
    have h_div_ab_ne_inf := NotInfinite.of.NeSt_0 (x := a / b) (by linarith)
    have h_div_ba_ne_inf := NotInfinite.of.NeSt_0 (x := b / a) (by linarith)
    have h_add_div_ab := StAdd.eq.AddStS.of.NotInfinite.NotInfinite h_div_ab_ne_inf h_div_ba_ne_inf
    simp [h_div_ba, h] at h_add_div_ab
    norm_num at h_add_div_ab
    have h_add_div_ba_ne_inf := NotInfiniteAdd.of.NotInfinite.NotInfinite h_div_ab_ne_inf h_div_ba_ne_inf
    have h_add_inv_div_ab := StAdd.eq.AddStS.of.NotInfinite.NotInfinite h_ne_inf_inv_ab h_add_div_ba_ne_inf
    rw [h_add_div_ab] at h_add_inv_div_ab
    have h_add_inv_ab_inf := NotInfiniteAdd.of.NotInfinite h_ne_inf_inv_ab (r := 2)
    have h_add_inv_div_ab_ne_inf := NotInfinitesimal.of.NeSt_0 (x := ((a * b)⁻¹ + (a / b + b / a))) (by linarith)
    have h_add_add_inv_div_ab_ne_inf := StDiv.eq.DivStS.of.NotInfinite.NotInfinitesimal h_add_inv_ab_inf h_add_inv_div_ab_ne_inf
    rw [h_add_inv_div_ab, h_2_ab_st] at h_add_add_inv_div_ab_ne_inf
    rwa [Div.eq.One.of.Ne_0] at h_add_add_inv_div_ab_ne_inf
    linarith


-- created on 2025-12-19
-- updated on 2025-12-20
