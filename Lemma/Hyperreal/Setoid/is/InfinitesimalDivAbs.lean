import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.Infinitesimal.is.InfinitesimalAbs
import Lemma.Hyperreal.Infinitesimal.is.InfinitesimalPow
import Lemma.Hyperreal.InfinitesimalAdd.of.Infinitesimal.Infinitesimal
import Lemma.Hyperreal.InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
import Lemma.Hyperreal.InfinitesimalSub.of.Infinitesimal.Infinitesimal
import Lemma.Hyperreal.NotInfinitesimalAdd.of.Infinitesimal.Ne_0
import Lemma.Hyperreal.Setoid.is.OrAndS
import Lemma.Nat.Add
import Lemma.Nat.AddAdd.eq.Add_Add
open Hyperreal Nat


@[main, comm, mp, mpr]
private lemma main
-- given
  (a b : ℝ*) :
-- imply
  a ≈ b ↔ Infinitesimal (|a - b| / (|a| + |b| + 1)) := by
-- proof
  rw [Setoid.is.OrAndS]
  constructor <;>
    intro h
  ·
    obtain h | h := h
    ·
      let ⟨h_a, h_b⟩ := h
      apply InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
      ·
        apply InfinitesimalAbs.of.Infinitesimal
        apply InfinitesimalSub.of.Infinitesimal.Infinitesimal h_a h_b
      ·
        apply NotInfinitesimalAdd.of.Infinitesimal.Ne_0
        ·
          apply InfinitesimalAdd.of.Infinitesimal.Infinitesimal
          repeat exact InfinitesimalAbs.of.Infinitesimal (by assumption)
        ·
          simp
    ·
      let ⟨h_ab, h_b⟩ := h
      if h_a : a.Infinitesimal then
        have h_ab_div := InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal h_a h_b
        have := NotInfinitesimalSub.of.Infinitesimal.Ne_0 h_ab_div (by simp) (r := 1)
        contradiction
      else
        have h := EqSt.of.InfinitesimalSub h_ab
        sorry
  ·
    if h_a : a.Infinitesimal then
      simp [h_a]
      if h_b : b.Infinitesimal then
        simp [h_b]
      else
        sorry
    else
      simp [h_a]
      if h_b : b.Infinitesimal then
        sorry
      else
        simp [h_b]
        sorry


-- created on 2025-12-09
-- updated on 2025-12-20
