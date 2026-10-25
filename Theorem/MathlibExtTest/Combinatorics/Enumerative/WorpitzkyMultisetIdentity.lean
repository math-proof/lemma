/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/WorpitzkyMultisetIdentity.lean -/


import Theorem.Combinatorics.Enumerative.WorpitzkyMultisetIdentity.Part14
import Lemma.Finset.Enumerative.WorpitzkyMultisetIdentity
import Mathlib.Data.Fin.VecNotation
open scoped BigOperators


namespace MetaMathlibExt

-- Two singleton multiplicities at x = 2 give four.
example :
    Finset.sum (Finset.Icc 1 (max 1 (Finset.sum Finset.univ (fun a => ![1, 1] a)))) (fun p =>
        Nat.choose (2 + Finset.sum Finset.univ (fun a => ![1, 1] a) - p)
            (Finset.sum Finset.univ (fun a => ![1, 1] a)) *
          Nat.card { w : Fin (Finset.sum Finset.univ (fun a => ![1, 1] a)) → Fin 2 //
            (∀ i,
              Fintype.card
                  { j : Fin (Finset.sum Finset.univ (fun a => ![1, 1] a)) // w j = i } =
                ![1, 1] i) ∧
            (Finset.univ.filter
                (fun j : Fin (Finset.sum Finset.univ (fun a => ![1, 1] a)) =>
                  ∃ h : j.val + 1 < Finset.sum Finset.univ (fun a => ![1, 1] a),
                    w j > w ⟨j.val + 1, h⟩)).card + 1 = p }) = 4 := by
  exact (worpitzky_identity_multiset 2 ![1, 1] 2).symm.trans
    (show (∏ i : Fin 2, Nat.choose (2 + ![1, 1] i - 1) (![1, 1] i)) = 4 by decide)

-- Unit multiplicities recover the classical power x^m.
example (m x : ℕ) (k : Fin m → ℕ) (hk : ∀ i, k i = 1) :
    Finset.sum (Finset.Icc 1 (max 1 (Finset.sum Finset.univ (fun a => k a)))) (fun p =>
        Nat.choose (x + Finset.sum Finset.univ (fun a => k a) - p)
            (Finset.sum Finset.univ (fun a => k a)) *
          Nat.card { w : Fin (Finset.sum Finset.univ (fun a => k a)) → Fin m //
            (∀ i,
              Fintype.card { j : Fin (Finset.sum Finset.univ (fun a => k a)) // w j = i } =
                k i) ∧
            (Finset.univ.filter
                (fun j : Fin (Finset.sum Finset.univ (fun a => k a)) =>
                  ∃ h : j.val + 1 < Finset.sum Finset.univ (fun a => k a),
                    w j > w ⟨j.val + 1, h⟩)).card + 1 = p }) = x ^ m := by
  exact (worpitzky_identity_multiset m k x).symm.trans
    (show (∏ i, Nat.choose (x + k i - 1) (k i)) = x ^ m by simp [hk])

end MetaMathlibExt
