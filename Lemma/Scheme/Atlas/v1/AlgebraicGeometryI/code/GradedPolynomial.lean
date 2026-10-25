import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.GradedPolynomial
open MvPolynomial


/--
[card_degree_eq_choose](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GradedPolynomial.lean)
-/
@[path]
lemma card_degree_eq_choose
  {n d : ℕ} :
-- imply
  Fintype.card {s : Fin n →₀ ℕ | s.degree = d} = (n + d - 1).choose d := by
-- proof
  rw [Fintype.card_congr (degreeEquivSym n d), Sym.card_sym_eq_choose, Fintype.card_fin]

/--
[homogeneousSubmodule_finiteDimensional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GradedPolynomial.lean)
-/
@[path]
lemma homogeneousSubmodule_finiteDimensional
  {k : Type*}
  [Field k]
  {n d : ℕ} :
-- imply
  Module.Finite k (homogeneousSubmodule (Fin n) k d) := by
-- proof
  rwa [homogeneousSubmodule_eq_finsupp_supported]
    (Finsupp.supportedEquivFinsupp (M := k) (R := k) {s : Fin n →₀ ℕ | s.degree = d}).symm

/--
[homogeneousSubmodule_finrank_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GradedPolynomial.lean)
-/
@[path]
lemma homogeneousSubmodule_finrank_eq_card
  {k : Type*}
  [Field k]
  {n d : ℕ} :
-- imply
  Module.finrank k (homogeneousSubmodule (Fin n) k d) = Fintype.card {s : Fin n →₀ ℕ | s.degree = d} := by
-- proof
  rw [homogeneousSubmodule_eq_finsupp_supported]
  let S : Set (Fin n →₀ ℕ) := {s | s.degree = d}
  show Module.finrank k ↥(Finsupp.supported k k S) = _
  rw [LinearEquiv.finrank_eq (Finsupp.supportedEquivFinsupp (M := k) (R := k) S),
    Module.finrank_finsupp_self]

/--
[homogeneousSubmodule_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GradedPolynomial.lean)
-/
@[path]
lemma homogeneousSubmodule_finrank
  {k : Type*}
  [Field k]
  {n d : ℕ} :
-- imply
  Module.finrank k (homogeneousSubmodule (Fin n) k d) = (n + d - 1).choose d := by
-- proof
  rw [homogeneousSubmodule_finrank_eq_card, card_degree_eq_choose]

/--
[hilbert_fun_eq_choose](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GradedPolynomial.lean)
-/
@[path]
lemma hilbert_fun_eq_choose
  {k : Type*}
  [Field k]
  {n d : ℕ} :
-- imply
  hilbertFun k n d = (n + d).choose n := by
-- proof
  unfold hilbertFun
  rw [homogeneousSubmodule_finrank]
  have h1 : n + 1 + d - 1 = n + d := by omega
  rw [h1, Nat.choose_symm_add.symm]

/--
[hilbert_fun_is_polynomial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GradedPolynomial.lean)
-/
@[path]
lemma hilbert_fun_is_polynomial
  {k : Type*}
  [Field k]
  {n : ℕ} :
-- imply
  ∃ p : Polynomial ℚ, (∀ d : ℕ, (hilbertFun k n d : ℚ) = p.eval (d : ℚ)) ∧ p.natDegree = n := by
-- proof
  refine ⟨Polynomial.preHilbertPoly ℚ n 0, ?_, Polynomial.natDegree_preHilbertPoly ℚ n 0⟩
  intro d
  rw [hilbert_fun_eq_choose, Polynomial.preHilbertPoly_eq_choose_sub_add ℚ n (Nat.zero_le d)]
  simp [add_comm]

/--
[hilbert_polynomial_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GradedPolynomial.lean)
-/
@[path]
lemma hilbert_polynomial_degree
  {n : ℕ} :
-- imply
  (Polynomial.preHilbertPoly ℚ n 0).natDegree = n :=
-- proof
  Polynomial.natDegree_preHilbertPoly ℚ n 0

/--
[hilbert_polynomial_leading_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GradedPolynomial.lean)
-/
@[path]
lemma hilbert_polynomial_leading_coeff
  {n : ℕ} :
-- imply
  (Polynomial.preHilbertPoly ℚ n 0).leadingCoeff = (↑(Nat.factorial n) : ℚ)⁻¹ :=
-- proof
  Polynomial.leadingCoeff_preHilbertPoly ℚ n 0

/--
[hilbert_fun_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GradedPolynomial.lean)
-/
@[path]
lemma hilbert_fun_mono
  {k : Type*}
  [Field k]
  {n d : ℕ} :
-- imply
  hilbertFun k n d ≤ hilbertFun k n (d + 1) := by
-- proof
  simp only [hilbert_fun_eq_choose]
  exact Nat.choose_le_choose n (by omega)


-- created on 2026-10-23
