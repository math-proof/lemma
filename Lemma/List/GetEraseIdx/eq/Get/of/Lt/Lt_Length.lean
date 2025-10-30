import Lemma.List.LengthEraseIdx.eq.SubLength_1.of.Lt_Length
import Lemma.Nat.LtAddS.is.Lt
open List Nat


@[main]
private lemma main
  {s : List α}
-- given
  (h₀ : i < s.length)
  (h₁ : j < i) :
-- imply
  let h_length : (s.eraseIdx i).length = s.length - 1 := LengthEraseIdx.eq.SubLength_1.of.Lt_Length h₀
  (s.eraseIdx i)[j] = s[j] := by
-- proof
  intro h_length
  induction s generalizing i j with
  | nil =>
    simp
  | cons a as ih =>
    cases i with
    | zero =>
      contradiction
    | succ i_succ =>
      cases j with
      | zero =>
        rfl
      | succ j' =>
        simp only [List.eraseIdx]
        apply ih <;>
        .
          apply Lt.of.LtAddS (by assumption)



-- created on 2025-06-22
