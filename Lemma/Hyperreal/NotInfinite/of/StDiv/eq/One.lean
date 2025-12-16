import Lemma.Hyperreal.Infinitesimal.is.All_LtAbs
import Lemma.Hyperreal.InfinitesimalSub.of.EqSt.Ne_0
import Lemma.Hyperreal.NotInfinite.is.Any_LeAbs
import Lemma.Hyperreal.Infinitesimal.of.Infinitesimal.NeSt_0
import sympy.core.power
open Hyperreal


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h : st (a / b) = 1) :
-- imply
  ¬((1 + 2 * a * b) / (1 + a² + b²)).Infinite := by
-- proof
  have h := InfinitesimalSub.of.EqSt.Ne_0 (by simp) h
  have h := All_LtAbs.of.Infinitesimal h
  if h_a : a.Infinitesimal then
    have h_b := Hyperreal.Infinitesimal.of.Infinitesimal.NeSt_0 (by linarith) h_a
    apply NotInfinite.of.Any_LeAbs
    sorry
  else
    apply NotInfinite.of.Any_LeAbs
    sorry


-- created on 2025-12-16
