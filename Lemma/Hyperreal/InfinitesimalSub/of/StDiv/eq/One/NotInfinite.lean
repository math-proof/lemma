import Lemma.Hyperreal.Infinite.of.Infinite.StDiv.ne.Zero
import Lemma.Hyperreal.Infinite.of.InfiniteDiv.NotInfinitesimal
import Lemma.Hyperreal.Infinitesimal.is.All_LtAbs
import Lemma.Hyperreal.Infinitesimal.of.Infinitesimal.StDiv.ne.Zero
import Lemma.Hyperreal.InfinitesimalSub.of.EqSt.NotInfinite
import Lemma.Hyperreal.InfinitesimalSub.of.Infinitesimal.Infinitesimal
import Lemma.Hyperreal.Ne_0.of.NotInfinitesimal
import Lemma.Hyperreal.NotInfinite.is.Any_LeAbs
import Lemma.Int.GtAbs_0.of.Ne_0
import Lemma.Rat.AbsDiv.eq.DivAbsS
import Lemma.Rat.Lt0Div.of.Gt_0.Gt_0
import Lemma.Rat.LtDiv.is.Lt_Mul.of.Gt_0
import Lemma.Rat.SubDiv.eq.DivSub.of.Ne_0
open Hyperreal Rat Int


@[main, mt 1]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : ¬a.Infinite)
  (h : (a / b).st = 1) :
-- imply
  (a - b).Infinitesimal := by
-- proof
  if h_a_eps : a.Infinitesimal then
    have h_b_eps := Infinitesimal.of.Infinitesimal.StDiv.ne.Zero.left (b := b) (by linarith) h_a_eps
    apply InfinitesimalSub.of.Infinitesimal.Infinitesimal h_a_eps h_b_eps
  else
    have h_b := NotInfinite.of.NotInfinite.StDiv.ne.Zero (by linarith) h_a (b := b)
    have h_b_eps := NotInfinitesimal.of.NotInfinitesimal.StDiv.ne.Zero (b := b) (by linarith) h_a_eps
    have h_ab := NotInfiniteDiv.of.NotInfinite.NotInfinitesimal h_b_eps h_a
    have h_eps := InfinitesimalSub.of.EqSt.NotInfinite h_ab h
    let ⟨⟨A, hA⟩, h_a⟩ := Any_LeAbs.of.NotInfinite h_a
    let ⟨⟨B, hB⟩, h_b⟩ := Any_LeAbs.of.NotInfinite h_b
    simp at h_a h_b
    have h_all := All_LtAbs.of.Infinitesimal h_eps
    apply Infinitesimal.of.All_LtAbs
    intro ⟨δ, hδ⟩
    simp
    have h_div_δB := Lt0Div.of.Gt_0.Gt_0 hδ hB
    specialize h_all ⟨δ / B, h_div_δB⟩
    simp at h_all
    have h_b_ne_0 := Ne_0.of.NotInfinitesimal h_b_eps
    rw [SubDiv.eq.DivSub.of.Ne_0 h_b_ne_0] at h_all
    rw [AbsDiv.eq.DivAbsS] at h_all
    have h_b_ne_0 := GtAbs_0.of.Ne_0 h_b_ne_0
    calc
      _ < _ := Lt_Mul.of.LtDiv.Gt_0 h_b_ne_0 h_all
      |b| * (↑δ / ↑B) ≤ B * (↑δ / ↑B) := by
        apply Nat.LeMulS.of.Le.Gt_0 h_b
        aesop
      _ = _  := by
        rw [EqMul_Div.of.Ne_0 (by linarith)]


-- created on 2025-12-28
