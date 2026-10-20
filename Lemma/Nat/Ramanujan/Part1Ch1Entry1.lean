import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch1Entry1
open MathlibExt.NumberTheory.Ramanujan.Part1Ch1
open Entry1Magicsquare3


/--
[ramanujan_part1_ch1_entry1_magicsquare3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch1Entry1.lean)
-/
@[path]
private lemma ramanujan_part1_ch1_entry1_magicsquare3_eq
  {n : ℕ}
  {a b : Fin n → ℕ}
  {L R : Fin n → Fin n → Fin n}
  {_hPair : Function.Bijective (fun p : Fin n × Fin n => (L p.1 p.2, R p.1 p.2))}
-- given
  (_hn : 0 < n)
  (hL_row : ∀ i : Fin n, Function.Bijective (L i))
  (hL_col : ∀ j : Fin n, Function.Bijective (fun i : Fin n => L i j))
  (hL_diag : Function.Bijective (fun i : Fin n => L i i))
  (hL_anti : Function.Bijective (fun i : Fin n => L i ⟨n - 1 - i.val, by omega⟩))
  (hR_row : ∀ i : Fin n, Function.Bijective (R i))
  (hR_col : ∀ j : Fin n, Function.Bijective (fun i : Fin n => R i j))
  (hR_diag : Function.Bijective (fun i : Fin n => R i i))
  (hR_anti : Function.Bijective (fun i : Fin n => R i ⟨n - 1 - i.val, by omega⟩)) :
-- imply
  ∃ S : ℕ,
      (∀ i : Fin n, (∑ j : Fin n, (a (L i j) + b (R i j))) = S)
      ∧ (∀ j : Fin n, (∑ i : Fin n, (a (L i j) + b (R i j))) = S)
      ∧ ((∑ i : Fin n, (a (L i i) + b (R i i))) = S)
      ∧ ((∑ i : Fin n,
          (a (L i ⟨n - 1 - i.val, by omega⟩) + b (R i ⟨n - 1 - i.val, by omega⟩))) = S) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch1.Entry1Magicsquare3.ramanujan_part1_ch1_entry1_magicsquare3 _hn a b L R hL_row hL_col hL_diag hL_anti hR_row hR_col hR_diag hR_anti _hPair


-- created on 2026-10-20
