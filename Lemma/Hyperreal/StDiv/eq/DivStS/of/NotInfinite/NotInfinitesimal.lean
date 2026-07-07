import Lemma.Hyperreal.Infinitesimal.is.InfiniteInv
import Lemma.Hyperreal.Ne_0.of.NotInfinitesimal
import Lemma.Hyperreal.StInv.eq.InvSt
import Lemma.Hyperreal.StMul.eq.MulStS.of.NotInfinite.NotInfinite
import Lemma.Hyperreal.Infinite.is.InfiniteNeg
import Lemma.Rat.Div.eq.Mul_Inv
open Hyperreal Rat


@[main]
private lemma main
  {x y : ℝ*}
-- given
  (hx : ¬x → ∞)
  (hy : ¬y → 0) :
-- imply
  stdPart (x / y) = stdPart x / stdPart y := by
-- proof
  rw [Div.eq.Mul_Inv]
  rw [StMul.eq.MulStS.of.NotInfinite.NotInfinite hx]
  ·
    simp [Div.eq.Mul_Inv]
  ·
    have h := NotInfiniteInv.of.NotInfinitesimal hy
    aesop


-- created on 2025-12-17
