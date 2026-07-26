import Lemma.Finset.Sum.ge.Zero.of.All_Ge_0
import Lemma.Hyperreal.XEqAddS.of.XEq.XEq.Le0Mul
import Lemma.Int.Le0Mul.of.Ge_0.Ge_0
open Hyperreal Finset Int


@[main]
private lemma main
  {n : ℕ}
  {A B : Fin n → ℝ*}
-- given
  (h_pos : ∀ i : Fin n, B i ≥ 0)
  (h_xeq : ∀ i : Fin n, A i ≈ B i) :
-- imply
  ∑ i : Fin n, A i ≈ ∑ i : Fin n, B i := by
-- proof
  induction n with
  | zero =>
    simp
  | succ n ih =>
    simp only [Fin.sum_univ_castSucc]
    refine XEqAddS.of.XEq.XEq.Le0Mul ?_ (ih (fun i => h_pos (Fin.castSucc i)) (fun i => h_xeq (Fin.castSucc i))) (h_xeq (Fin.last n))
    apply Le0Mul.of.Ge_0.Ge_0
    ·
      apply Sum.ge.Zero.of.All_Ge_0
      intro i hi
      exact h_pos (Fin.castSucc i)
    ·
      exact h_pos (Fin.last n)


-- created on 2026-07-26
