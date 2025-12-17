import Lemma.Hyperreal.Infinitesimal.is.InfiniteInv
import Lemma.Hyperreal.Ne_0.of.NotInfinitesimal
import Lemma.Hyperreal.StInv.eq.InvSt
import Lemma.Hyperreal.StMul.eq.MulStS.of.NotInfinite.NotInfinite
import Lemma.Rat.Div.eq.Mul_Inv
open Hyperreal Rat


@[main]
private lemma main
  {x y : ℝ*}
-- given
  (hx : ¬x.Infinite)
  (hy : ¬y.Infinitesimal) :
-- imply
  (x / y).st = x.st / y.st := by
-- proof
  rw [Div.eq.Mul_Inv]
  rw [StMul.eq.MulStS.of.NotInfinite.NotInfinite hx]
  ·
    simp [Div.eq.Mul_Inv]
    left
    apply StInv.eq.InvSt
  ·
    apply NotInfiniteInv.of.NotInfinitesimal hy


-- created on 2025-12-17
