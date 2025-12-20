import Lemma.Hyperreal.EqSt_0.of.Infinite
import Lemma.Hyperreal.Infinite.of.Infinite.StDiv.ne.Zero
import Lemma.Hyperreal.Infinitesimal.of.Infinitesimal.StDiv.ne.Zero
import Lemma.Hyperreal.InfiniteMul.of.Infinite.Infinite
import Lemma.Hyperreal.StInv.eq.Inv.of.EqSt
import Lemma.Hyperreal.Lt0StInvMul.of.StDiv.gt.Zero.NotInfinite.NotInfinite.NotInfinitesimal.NotInfinitesimal
open Hyperreal


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_st : st (a / b) = 1)
  (h_a : ¬a.Infinitesimal) :
-- imply
  (a * b)⁻¹.st ≥ 0 := by
-- proof
  if h_a_inf : a.Infinite then
    have h_b_inf := Infinite.of.Infinite.StDiv.ne.Zero.left (by linarith) h_a_inf (b := b)
    have h_ab_inf := InfiniteMul.of.Infinite.Infinite h_a_inf h_b_inf
    have h_nonneg_st_inv_ab := EqSt_0.of.Infinite h_ab_inf
    have h_nonneg_st_inv_ab := StInv.eq.Inv.of.EqSt h_nonneg_st_inv_ab
    conv_rhs at h_nonneg_st_inv_ab => simp
    linarith
  else
    have h_b := NotInfinitesimal.of.NotInfinitesimal.StDiv.ne.Zero (by linarith) h_a (b := b)
    have h_b_inf := NotInfinite.of.NotInfinite.StDiv.ne.Zero (by linarith) h_a_inf (b := b)
    linarith [Lt0StInvMul.of.StDiv.gt.Zero.NotInfinite.NotInfinite.NotInfinitesimal.NotInfinitesimal h_a h_b h_a_inf h_b_inf (by linarith)]


-- created on 2025-12-18
