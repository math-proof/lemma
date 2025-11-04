import Lemma.Nat.LtMod.of.Ne_0
import Lemma.Nat.Le.of.Lt.Le
import Lemma.Nat.Mod.eq.Sub_MulDiv
open Nat


@[main]
private lemma main
  {d : ℕ} :
-- imply
  n ≥ n % d := by
-- proof
  if h_d : d = 0 then
    subst h_d
    simp
  else if h_n : n ≥ d then
    apply Le.of.Lt.Le h_n
    apply LtMod.of.Ne_0 h_d n
  else
    simp [Mod.eq.Sub_MulDiv]


-- created on 2025-07-09
