import Lemma.Hyperreal.Infinite.is.InfiniteAdd
import Lemma.Hyperreal.InfinitesimalSquare.of.Infinitesimal
import Lemma.Nat.AddAdd.eq.Add_Add
open Hyperreal Nat


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : a.Infinitesimal)
  (h : Infinitesimal ((a - b)² / (1 + a² + b²))) :
-- imply
  ¬(1 + a ^ 2 + b ^ 2).Infinite := by
-- proof
  by_contra h'
  rw [AddAdd.eq.Add_Add] at h'
  have h' := Infinite.of.InfiniteAdd.left h'
  have h_a₂ := InfinitesimalSquare.of.Infinitesimal h_a
  sorry


-- created on 2025-12-19
