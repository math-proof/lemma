import sympy.series.limits
import sympy.vector.vector
import Lemma.Hyperreal.Infinitesimal.is.Infinitesimal.of.XEq
import Lemma.Hyperreal.InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
import Lemma.Hyperreal.XEq.is.OrAndS
import Lemma.Hyperreal.XEqDivS.of.XEq.XEq.NotOr
import Lemma.Vector.GetDiv.eq.DivGet
import Lemma.Vector.XEq.is.All_XEqGetS
import Lemma.Vector.XEqSumS.of.XEq.Ge_0
open Hyperreal Vector


@[main]
private lemma main
  {a b : List.Vector ℝ* n}
-- given
  (h_pos : b ≥ 0)
  (h_not_sum : ¬(b.sum → 0))
  (h : a ≈ b) :
-- imply
  let den_a := a.sum
  let den_b := b.sum
  (a / den_a) ≈ (b / den_b) := by
-- proof
  intro den_a den_b
  simp only [den_a, den_b]
  have h_sum := XEqSumS.of.XEq.Ge_0 h_pos h
  have h_not_sum_a : ¬(a.sum → 0) := fun ha =>
    h_not_sum ((Infinitesimal.is.Infinitesimal.of.XEq h_sum).mp ha)
  refine Vector.XEq.of.All_XEqGetS.fin ?_
  intro i
  rw [GetDiv.eq.DivGet.fin, GetDiv.eq.DivGet.fin]
  if hi : a.get i → 0 then
    have hi' : b.get i → 0 :=
      (Infinitesimal.is.Infinitesimal.of.XEq (All_XEqGetS.of.XEq h i)).mp (show a[i] → 0 from hi)
    apply XEq.of.OrAndS
    left
    exact ⟨
      InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal hi (fun h => h_not_sum_a h),
      InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal hi' (fun h => h_not_sum h)⟩
  else
    have hn_bi : ¬(b.get i → 0) := fun hbi =>
      hi ((Infinitesimal.is.Infinitesimal.of.XEq (All_XEqGetS.of.XEq h i)).mpr hbi)
    apply XEqDivS.of.XEq.XEq.NotOr
    ·
      intro hbad
      obtain hbi | hden := hbad
      · exact hn_bi hbi
      · exact h_not_sum hden
    ·
      exact All_XEqGetS.of.XEq h i
    ·
      exact h_sum


-- created on 2026-07-26
