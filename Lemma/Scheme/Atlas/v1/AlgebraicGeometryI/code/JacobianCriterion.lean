import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.JacobianCriterion
open IsLocalRing


/--
[proposition31_smooth_iff_locally_generated](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/JacobianCriterion.lean)
-/
@[path]
lemma proposition31_smooth_iff_locally_generated
  [Field k]
  {n : ℕ}
  {I : Ideal (MvPolynomial (Fin n) k)}
  {x : Fin n → k}
-- given
  (hI : I ≤ maxIdealOfPoint x) :
-- imply
  IsRegularLocalRing (localRingAtPoint I x hI) ↔ (∃ (m : ℕ) (f : Fin m → MvPolynomial (Fin n) k), (∀ i, f i ∈ I) ∧ LinearIndependent k (fun i : Fin m => (fun j : Fin n => MvPolynomial.eval x (MvPolynomial.pderiv j (f i)))) ∧ ∃ (u : MvPolynomial (Fin n) k), MvPolynomial.eval x u ≠ 0 ∧ ∀ g ∈ I, u * g ∈ Ideal.span (Set.range f)) :=
-- proof
  Proposition31_smooth_point_characterization I x hI

/--
[proposition31_jacobian_criterion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/JacobianCriterion.lean)
-/
@[path]
lemma proposition31_jacobian_criterion
  [Field k]
  {n m : ℕ}
  {f : Fin m → MvPolynomial (Fin n) k}
  {x : Fin n → k}
-- given
  (hx : ∀ i, MvPolynomial.eval x (f i) = 0)
  (hI : Ideal.span (Set.range f) ≤ maxIdealOfPoint x)
  (hdim : ringKrullDim (localRingAtPoint (Ideal.span (Set.range f)) x hI) = (n - m : ℕ)) :
-- imply
  IsRegularLocalRing (localRingAtPoint (Ideal.span (Set.range f)) x hI) ↔ (jacobianMatrix f x).rank = m :=
-- proof
  (Corollary23_jacobian_criterion f x hx hI hdim).symm

/--
[jacobian_rank_eq_of_linearIndependent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/JacobianCriterion.lean)
-/
@[path]
lemma jacobian_rank_eq_of_linearIndependent
  [Field k]
  {n m : ℕ}
  {f : Fin m → MvPolynomial (Fin n) k}
  {x : Fin n → k}
-- given
  (hf_indep : LinearIndependent k (fun i : Fin m => (fun j : Fin n => MvPolynomial.eval x (MvPolynomial.pderiv j (f i))))) :
-- imply
  (jacobianMatrix f x).rank = m := by
-- proof
  have h : LinearIndependent k (jacobianMatrix f x).row := by
    simp only [Matrix.row]
    exact hf_indep
  rw [LinearIndependent.rank_matrix h, Fintype.card_fin]


-- created on 2026-10-23
