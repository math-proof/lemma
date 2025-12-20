import Lemma.Hyperreal.Infinite.of.InfinitesimalDiv.NotInfinitesimal
import Lemma.Hyperreal.Infinitesimal.is.InfinitesimalPow
import Lemma.Hyperreal.InfinitesimalSub.of.Infinitesimal.Infinitesimal
import Lemma.Hyperreal.NotInfiniteAdd_Square.of.InfinitesimalDivSquare.Infinitesimal
open Hyperreal


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h : Infinitesimal ((a - b)² / (a² + b² + 1)))
  (h_a : Infinitesimal a) :
-- imply
  Infinitesimal b := by
-- proof
  have : NeZero (a² + b² + 1) := ⟨by nlinarith⟩
  have h_not_finite := NotInfiniteAdd_Square.of.InfinitesimalDivSquare.Infinitesimal h_a h
  have := Infinitesimal.of.InfinitesimalDiv.NotInfinite h_not_finite h
  have := Infinitesimal.of.InfinitesimalPow this
  have h_b := InfinitesimalSub.of.Infinitesimal.Infinitesimal h_a this
  simp at h_b
  assumption


-- created on 2025-12-20
