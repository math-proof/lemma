import Lemma.Finset.Lt.of.In_Ico
import Lemma.Int.Mod.eq.Sub_Mul_FloorDiv
import Lemma.Set.Ge.of.In_Ico
import Lemma.Rat.Sub_Mul_FloorDiv.in.Ico.of.Gt_0
open Finset Int Set Rat


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : d > 0) :
-- imply
  n % d ∈ Set.Ico 0 d := by
-- proof
  have hIco :=
    Sub_Mul_FloorDiv.in.Ico.of.Gt_0 (α := ℚ) (d := (d : ℚ)) (by exact_mod_cast h) (n := (n : ℚ))
  rw [Mod.eq.Sub_Mul_FloorDiv (α := ℚ) h, Set.mem_Ico]
  constructor
  ·
    exact_mod_cast Ge.of.In_Ico (α := ℚ) hIco
  ·
    exact_mod_cast Lt.of.In_Ico (α := ℚ) hIco


-- created on 2018-03-02
