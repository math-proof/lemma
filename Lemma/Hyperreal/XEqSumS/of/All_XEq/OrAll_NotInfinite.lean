import Lemma.Finset.LeSumS.of.All_Le
import Lemma.Finset.Sum.ge.Zero.of.All_Ge_0
import Lemma.Hyperreal.XEqAddS.of.XEq.XEq.Or_OrNotSInfinite
import Lemma.Int.Le0Mul.of.Ge_0.Ge_0
import Lemma.Int.Le0Mul.of.Le_0.Le_0
open Hyperreal Finset Int


@[main]
private lemma main
  {n : ℕ}
  {A B : Fin n → ℝ*}
-- given
  (h_or :
    (∀ i : Fin n, ¬(B i → ∞)) ∨
    (∀ i : Fin n, B i ≥ 0) ∨
    (∀ i : Fin n, B i ≤ 0))
  (h_xeq : ∀ i : Fin n, A i ≈ B i) :
-- imply
  ∑ i : Fin n, A i ≈ ∑ i : Fin n, B i := by
-- proof
  induction n with
  | zero =>
    simp
  | succ n ih =>
    simp only [Fin.sum_univ_castSucc]
    obtain h_fin | h_ge | h_le := h_or
    ·
      refine XEqAddS.of.XEq.XEq.Or_OrNotSInfinite ?_
        (ih (Or.inl fun i => h_fin (Fin.castSucc i)) (fun i => h_xeq (Fin.castSucc i)))
        (h_xeq (Fin.last n))
      apply Or.inr
      apply Or.inr
      exact h_fin (Fin.last n)
    ·
      refine XEqAddS.of.XEq.XEq.Or_OrNotSInfinite ?_
        (ih (Or.inr (Or.inl fun i => h_ge (Fin.castSucc i))) (fun i => h_xeq (Fin.castSucc i)))
        (h_xeq (Fin.last n))
      apply Or.inl
      apply Le0Mul.of.Ge_0.Ge_0
      ·
        apply Sum.ge.Zero.of.All_Ge_0
        intro i hi
        exact h_ge (Fin.castSucc i)
      ·
        exact h_ge (Fin.last n)
    ·
      refine XEqAddS.of.XEq.XEq.Or_OrNotSInfinite ?_
        (ih (Or.inr (Or.inr fun i => h_le (Fin.castSucc i))) (fun i => h_xeq (Fin.castSucc i)))
        (h_xeq (Fin.last n))
      apply Or.inl
      apply Le0Mul.of.Le_0.Le_0
      ·
        have h_sum_le : ∑ i : Fin n, B (Fin.castSucc i) ≤ 0 := by
          have h := LeSumS.of.All_Le (s := Finset.univ)
            (x := fun i : Fin n => B (Fin.castSucc i))
            (y := fun _ => 0)
            (fun i _ => h_le (Fin.castSucc i))
          simp at h
          simpa using h
        exact h_sum_le
      ·
        exact h_le (Fin.last n)


-- created on 2026-07-26
