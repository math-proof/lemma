import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.ChromaticNumber
open ChromaticNumber
open Finset Real Filter Nat Classical


namespace ChromaticNumber

/--
[k₀_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/ChromaticNumber.lean)
-/
@[path]
in $\{0, \dots, n\}$. -/
lemma k₀_le (n : ℕ) : k₀ n ≤ n :=
  Nat.findGreatest_le n

end ChromaticNumber

namespace ChromaticNumber

/--
[cliqueNum_lt_iff_cliqueFree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/ChromaticNumber.lean)
-/
@[path]
lemma cliqueNum_lt_iff_cliqueFree
  {n : ℕ}
  {G : SimpleGraph (Fin n)}
  {m : ℕ}
-- given
  (hm : m ≤ n)
  (hm0 : 0 < m) :
-- imply
  cliqueNum G < m ↔ G.CliqueFree m := by
-- proof
  simp only [cliqueNum]
  constructor
  · intro h
    by_contra habs
    exact Nat.not_lt.mpr (Nat.le_findGreatest hm habs) h
  · intro hcf
    by_contra hlt
    push_neg at hlt
    have hne : (Nat.findGreatest (fun k => ¬G.CliqueFree k) n) ≠ 0 := by omega
    exact (Nat.findGreatest_of_ne_zero rfl hne) (SimpleGraph.CliqueFree.mono hlt hcf)

end ChromaticNumber

namespace ChromaticNumber

/--
[factorial_le_two_pow_choose](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/ChromaticNumber.lean)
-/
@[path]
lemma factorial_le_two_pow_choose
  {L : ℕ} :
-- imply
  L ! ≤ 2 ^ Nat.choose L 2 := by
-- proof
  induction L with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ]
    have hchoose : Nat.choose (n + 1) 2 = Nat.choose n 2 + n := by
      simp [Nat.choose_succ_succ, Nat.choose_one_right]; omega
    rw [hchoose, Nat.pow_add]
    calc (n + 1) * n ! ≤ 2 ^ n * n ! := Nat.mul_le_mul_right _ n.lt_two_pow_self
      _ ≤ 2 ^ n * 2 ^ Nat.choose n 2 := Nat.mul_le_mul_left _ ih
      _ = 2 ^ Nat.choose n 2 * 2 ^ n := by ring
/-- Asymptotic lower bound on the expected clique count at the shifted threshold: for any
$\varepsilon > 0$, eventually $\mu(n, k_0(n) - 3) \ge n^{3 - \varepsilon}$. -/

end ChromaticNumber

/--
[k](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/ChromaticNumber.lean)
-/
@[path]
private lemma k_eq
  {n : ℕ} :
-- imply
  k₀ n ≤ n := by
-- proof
  apply ChromaticNumber.k n


-- created on 2026-10-23
