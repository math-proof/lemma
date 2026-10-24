import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.EllipticCurves.code.HilbertClassPolynomial
open Polynomial Classical


/--
[CMjInvariants_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/HilbertClassPolynomial.lean)
-/
@[path]
lemma CMjInvariants_nonempty
  {D : ℤ}
-- given
  (hD : IsImaginaryQuadraticDiscriminant D) :
-- imply
  (CMjInvariants D hD).Nonempty := by
-- proof
  let 𝒪 := imaginaryQuadraticOrder D hD
  letI : Finite (ComplexLattice.IdealClassGroup 𝒪) :=
    ComplexLattice.IdealClassGroup.finite 𝒪
  letI : Fintype (ComplexLattice.IdealClassGroup 𝒪) := Fintype.ofFinite _
  letI : CommGroup (ComplexLattice.IdealClassGroup 𝒪) :=
    ComplexLattice.IdealClassGroup.commGroup 𝒪
  exact Finset.Nonempty.image Finset.univ_nonempty _

/--
[hilbertClassPoly_monic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/HilbertClassPolynomial.lean)
-/
@[path]
lemma hilbertClassPoly_monic
  {D : ℤ}
-- given
  (hD : IsImaginaryQuadraticDiscriminant D) :
-- imply
  (hilbertClassPoly D hD).Monic :=
-- proof
  monic_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _

/--
[hilbertClassPoly_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/HilbertClassPolynomial.lean)
-/
@[path]
lemma hilbertClassPoly_natDegree
  {D : ℤ}
-- given
  (hD : IsImaginaryQuadraticDiscriminant D) :
-- imply
  (hilbertClassPoly D hD).natDegree = (CMjInvariants D hD).card := by
-- proof
  rw [hilbertClassPoly, natDegree_prod_of_monic _ _ (fun j _ => monic_X_sub_C j)]
  simp

/--
[coeff_prod_X_sub_C_isIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/HilbertClassPolynomial.lean)
-/
@[path]
lemma coeff_prod_X_sub_C_isIntegral
  {s : Finset ℂ}
  {n : ℕ}
-- given
  (hint : ∀ j ∈ s, IsIntegral ℤ j) :
-- imply
  IsIntegral ℤ ((s.prod (fun j => X - C j)).coeff n) := by
-- proof
  have heq : s.prod (fun j => X - C j) = s.prod (fun j => X + C (-j)) := by
    congr 1; ext j; simp [sub_eq_add_neg, map_neg]
  rw [heq]
  by_cases hn : n ≤ s.card
  · rw [Finset.prod_X_add_C_coeff s (fun j => -j) hn]
    apply IsIntegral.sum
    intro t ht
    apply IsIntegral.prod
    intro i hi
    exact (hint i ((Finset.mem_powersetCard.mp ht).1 hi)).neg
  · push Not at hn
    have hdeg : (s.prod (fun j => X + C (-j))).natDegree = s.card := by
      conv_lhs => rw [heq.symm]
      rw [natDegree_prod_of_monic _ _ (fun j _ => monic_X_sub_C j)]
      simp
    rwa [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

/--
[hilbertClassPoly_eval_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/HilbertClassPolynomial.lean)
-/
@[path]
lemma hilbertClassPoly_eval_eq_zero
  {D : ℤ}
  {j : ℂ}
-- given
  (hD : IsImaginaryQuadraticDiscriminant D)
  (hj : j ∈ CMjInvariants D hD) :
-- imply
  Polynomial.eval j (hilbertClassPoly D hD) = 0 := by
-- proof
  rw [hilbertClassPoly]
  simp only [eval_prod, Finset.prod_eq_zero_iff]
  exact ⟨j, hj, by simp⟩

/--
[hilbertClassPoly_isRoot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/HilbertClassPolynomial.lean)
-/
@[path]
lemma hilbertClassPoly_isRoot
  {D : ℤ}
  {j : ℂ}
-- given
  (hD : IsImaginaryQuadraticDiscriminant D)
  (hj : j ∈ CMjInvariants D hD) :
-- imply
  (hilbertClassPoly D hD).IsRoot j :=
-- proof
  hilbertClassPoly_eval_eq_zero D hD j hj

/--
[hilbertClassPoly_isRoot_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/HilbertClassPolynomial.lean)
-/
@[path]
lemma hilbertClassPoly_isRoot_iff
  {D : ℤ}
  {z : ℂ}
-- given
  (hD : IsImaginaryQuadraticDiscriminant D) :
-- imply
  (hilbertClassPoly D hD).IsRoot z ↔ z ∈ CMjInvariants D hD := by
-- proof
  simp only [hilbertClassPoly, IsRoot, eval_prod, Finset.prod_eq_zero_iff,
    eval_sub, eval_X, eval_C, sub_eq_zero]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ha
  · intro h; exact ⟨z, h, rfl⟩


-- created on 2026-10-23
