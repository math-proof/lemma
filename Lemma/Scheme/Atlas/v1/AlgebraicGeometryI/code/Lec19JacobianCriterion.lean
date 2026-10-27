import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.Lec19JacobianCriterion
open IsLocalRing


/--
[corollary23_jacobian_rank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec19JacobianCriterion.lean)
-/
@[path]
lemma corollary23_jacobian_rank
  [Field k]
  {n m : ℕ}
  {f : Fin m → MvPolynomial (Fin n) k}
  {x : Fin n → k}
-- given
  (hx : ∀ i, MvPolynomial.eval x (f i) = 0)
  (hI : Ideal.span (Set.range f) ≤ maxIdealOfPoint x)
  (hdim : ringKrullDim (localRingAtPoint (Ideal.span (Set.range f)) x hI) = (n - m : ℕ)) :
-- imply
  (jacobianMatrix f x).rank = m ↔ IsRegularLocalRing (localRingAtPoint (Ideal.span (Set.range f)) x hI) :=
-- proof
  Corollary23_jacobian_criterion f x hx hI hdim

/--
[corollary23_jacobian_hypersurface](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec19JacobianCriterion.lean)
-/
@[path]
lemma corollary23_jacobian_hypersurface
  [Field k]
  {n : ℕ}
  {P : MvPolynomial (Fin n) k}
  {x : Fin n → k}
-- given
  (hx : MvPolynomial.eval x P = 0)
  (hI : Ideal.span (Set.range (fun _ : Fin 1 => P)) ≤ maxIdealOfPoint x)
  (hdim : ringKrullDim (localRingAtPoint (Ideal.span (Set.range (fun _ : Fin 1 => P))) x hI) = (n - 1 : ℕ)) :
-- imply
  (∃ i, MvPolynomial.eval x (MvPolynomial.pderiv i P) ≠ 0) ↔ IsRegularLocalRing (localRingAtPoint (Ideal.span (Set.range (fun _ : Fin 1 => P))) x hI) := by
-- proof
  rw [Corollary23_hypersurface_criterion P x hx]
  have hx' : ∀ i : Fin 1, MvPolynomial.eval x ((fun _ : Fin 1 => P) i) = 0 :=
    fun _ => hx
  exact corollary23_jacobian_rank (fun _ : Fin 1 => P) x hx' hI hdim


-- created on 2026-10-23
