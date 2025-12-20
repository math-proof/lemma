import Lemma.Hyperreal.EqSt0'0
import Lemma.Hyperreal.EqSt_0.is.Infinite.ou.Infinitesimal
import Lemma.Hyperreal.InfiniteMul.of.NotInfinitesimal.Infinite
import Lemma.Hyperreal.Infinitesimal.is.InfiniteInv
import Lemma.Rat.Div.eq.Mul_Inv
open Hyperreal Rat


/--
the hypotheses are arranged in the constructor order of division a / b
-/
@[main, mt 1]
private lemma main
  {a : ℝ*}
-- given
  (h_a : ¬Infinitesimal a)
  (h_b : Infinitesimal b) :
-- imply
  st (a / b) = 0 := by
-- proof
  if h_b_0 : b = 0 then
    subst h_b_0
    simp
    apply EqSt0'0
  else
    apply EqSt_0.of.Infinite.ou.Infinitesimal
    left
    have : NeZero b := ⟨h_b_0⟩
    have h_inf := InfiniteInv.of.Infinitesimal h_b
    rw [Div.eq.Mul_Inv]
    apply InfiniteMul.of.NotInfinitesimal.Infinite h_a h_inf


-- created on 2025-12-20
