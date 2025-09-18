import Lemma.Algebra.LengthEraseIdx.eq.SubLength_1.of.Lt_Length
import Lemma.Algebra.LtAddS.is.Lt
open Algebra


@[main]
private lemma main
  {v : List α}
-- given
  (h₀ : i < v.length)
  (h₁ : j < i) :
-- imply
  let h_length : (v.eraseIdx i).length = v.length - 1 := LengthEraseIdx.eq.SubLength_1.of.Lt_Length h₀
  (v.eraseIdx i)[j] = v[j] := by
-- proof
  intro h_length
  induction v generalizing i j with
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
        simp only [List.get, List.eraseIdx]
        have h₀ := Lt.of.LtAddS h₀
        have h₁ := Lt.of.LtAddS h₁
        apply ih h₀ h₁


-- created on 2025-06-22
