import Lemma.Nat.LtMod.of.Ne_0
import Lemma.Nat.Mod_Mul.eq.AddMul_Mod.of.Lt
import Lemma.Nat.Mul
open Nat


@[main]
private lemma main
-- given
  (h : d ≠ 0)
  (q n : ℕ) :
-- imply
  (q * d + r % d) % (n * d) = (q % n) * d + r % d :=
-- proof
  Mod_Mul.eq.AddMul_Mod.of.Lt (d := d) (r := r % d) (q := q) (n := n) (LtMod.of.Ne_0 h r)


-- created on 2025-11-21
