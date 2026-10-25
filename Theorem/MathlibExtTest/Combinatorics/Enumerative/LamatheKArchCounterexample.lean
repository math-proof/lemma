/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/LamatheKArchCounterexample.lean -/


import Mathlib.Data.Finset.Basic


/-!
# Lamathe k-arch counterexample

The code `({1, 2}, {3, 4}, {5, 6})` over labels `[1, 6]` admits no initial
decoding vertex: every label occurs in a block, so the complement of the
blocks in `[1, 6]` is empty. This is the smallest counterexample given by
Caminiti and Fusco to Lamathe's counting formula for labeled k-arch graphs
(`k = 2`, `n = 6`).

Source: Saverio Caminiti and Emanuele G. Fusco, *On the Number of Labeled
k-arch Graphs*, Journal of Integer Sequences 10 (2007), Article 07.7.5,
counterexample lines 363–367,
<https://cs.uwaterloo.ca/journals/JIS/VOL10/Caminiti/caminiti.tex>.
-/

example :
    ¬ ∃ v ∈ ({1, 2, 3, 4, 5, 6} : Finset ℕ),
      v ∉ (({1, 2} : Finset ℕ) ∪ {3, 4} ∪ {5, 6}) := by
  simp

