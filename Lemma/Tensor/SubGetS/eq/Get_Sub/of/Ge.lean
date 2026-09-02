import Lemma.Nat.ValSub.eq.SubValS.of.Ge
import Lemma.Tensor.GetAdd.eq.AddGetS
import Lemma.Tensor.GetNeg.eq.NegGet
open Nat Tensor


private lemma eq_theta_get
  {n d : ℕ}
  {θ : Tensor ℝ [n, d / 2]}
  {b : ℕ}
  {lam : ℝ}
-- given
  (hθ : θ = [i < n] [j < d / 2] ↑(lam * i / b ^ (j / (d / 2 : ℝ))))
  (i : Fin n)
  (j : Fin (d / 2)) :
-- imply
  θ[i][j] = (↑(lam * i / b ^ (j / (d / 2 : ℝ))) : Tensor ℝ []) := by
-- proof
  rw [hθ]
  have hrow := EqGetStack.fin (fun i : Fin n => [j < d / 2] (↑(lam * i / b ^ (j / (d / 2 : ℝ))) : Tensor ℝ [])) i
  have hcol := EqGetStack.fin (fun j : Fin (d / 2) => (↑(lam * i / b ^ (j / (d / 2 : ℝ))) : Tensor ℝ [])) j
  exact (congrArg (fun X : Tensor ℝ [d / 2] => X[j]) hrow).trans hcol


private lemma get_neg
-- given
  (x : Tensor ℝ [d])
  (j : Fin d) :
-- imply
  id (α := Tensor ℝ []) (-x)[j] = -(id (α := Tensor ℝ []) x[j]) := by
-- proof
  have h := GetNeg.eq.NegGet (X := x) ⟨j, by simp [Tensor.length]⟩
  simp only [id]
  exact h


private lemma get_add
-- given
  (x y : Tensor ℝ [d])
  (j : Fin d) :
-- imply
  id (α := Tensor ℝ []) (x + y)[j] = id (α := Tensor ℝ []) (x[j] + y[j]) := by
-- proof
  have h := GetAdd.eq.AddGetS.fin (A := x) (B := y) (i := j)
  simp only [id]
  exact h


private lemma coe_add_neg
-- given
  (x y : ℝ) :
-- imply
  (↑x : Tensor ℝ []) + -↑y = ↑(x - y) := by
-- proof
  apply Eq.of.EqDataS
  ext i
  change ((↑x : Tensor ℝ []).data + (-(↑y : Tensor ℝ [])).data).get i = (↑(x - y) : Tensor ℝ []).data.get i
  erw [Vector.GetAdd.eq.AddGetS.fin (a := (↑x : Tensor ℝ []).data) (b := (-(↑y : Tensor ℝ [])).data) (i := i)]


@[main]
private lemma main
  {n d : ℕ}
  {θ : Tensor ℝ [n, d / 2]}
  {b : ℕ}
  {lam : ℝ}
  {k t : Fin n}
-- given
  (hθ : θ = [i < n] [j < d / 2] ↑(lam * i / b ^ (j / (d / 2 : ℝ))))
  (hle : k ≥ t) :
-- imply
  θ[k]- θ[t] = θ[k - t] := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro j
  have hk := eq_theta_get hθ k j
  have ht := eq_theta_get hθ t j
  have hm := eq_theta_get hθ (k - t) j
  have hadd := get_add (θ[k] : Tensor ℝ [d / 2]) (-(θ[t] : Tensor ℝ [d / 2])) j
  have hneg := get_neg (θ[t] : Tensor ℝ [d / 2]) j
  simp only [id] at hadd hneg
  simp [GetElem.getElem] at hadd hneg hk ht hm ⊢
  refine hadd.trans ?_
  refine Eq.trans (congrArg₂ (fun (a b : Tensor ℝ [d / 2].tail) => a + b) hk (hneg.trans (congrArg Neg.neg ht))) ?_
  refine (coe_add_neg _ _).trans ?_
  refine Eq.trans ?_ hm.symm
  apply congrArg (fun r : ℝ => (↑r : Tensor ℝ []))
  have hval : ((k - t : Fin n) : ℕ) = (k : ℕ) - (t : ℕ) := ValSub.eq.SubValS.of.Ge hle
  have hcast : (((k : ℕ) - (t : ℕ) : ℕ) : ℝ) = (k : ℝ) - (t : ℝ) := CoeSub.eq.SubCoeS.of.Ge hle
  rw [hval, hcast]
  ring


-- created on 2026-09-01
