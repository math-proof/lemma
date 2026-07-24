-- import Lemma.Tensor.FromVectorMapToVector.eq.Stack
import Lemma.Tensor.Select_1.eq.FromVectorMapToVector.of.GtLength_0
-- import Lemma.Tensor.Select.eq.Stack_Select.of.GtLength
open Tensor


@[main]
private lemma main
  {d : ℕ}
-- given
  (h : s.length > d)
  (X : Tensor α (n :: s))
  (i : Fin s[d]) :
-- imply
  X.select ⟨d + 1, by grind⟩ ⟨i, by grind⟩ = Tensor.fromVector (X.toVector.map (·.select ⟨d, by grind⟩ ⟨i, by grind⟩)) := by
-- proof
  induction d with
  | zero =>
    exact Select_1.eq.FromVectorMapToVector.of.GtLength_0 h X i
  | succ j _ih =>
    sorry
    -- have h_j : s.length > j := Nat.lt_succ_iff.mp h
    -- calc
    --   X.select ⟨j + 2, by grind⟩ ⟨i, by grind⟩ =
    --       [k < n] (X[k].select ⟨j + 1, by grind⟩ ⟨i, by grind⟩) :=
    --     Select.eq.Stack_Select.of.GtLength h_j X i
    --   _ = Tensor.fromVector (X.toVector.map (·.select ⟨j + 1, by grind⟩ ⟨i, by grind⟩)) :=
    --     (FromVectorMapToVector.eq.Stack (fun s => s.eraseIdx (j + 1)) (fun X => X.select ⟨j + 1, by grind⟩ ⟨i, by grind⟩) X).symm


-- created on 2026-07-23
