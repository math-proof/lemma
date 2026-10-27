import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProjectionTheory.code.PolynomialHamSandwich
open MeasureTheory MvPolynomial PolynomialHamSandwich


namespace PolynomialHamSandwich

/--
[signedVol_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/PolynomialHamSandwich.lean)
-/
@[path]
lemma signedVol_neg
  {d : ℕ}
  {P : MvPolynomial (Fin d) ℝ}
  {U : Set (Fin d → ℝ)} :
-- imply
  signedVol d (-P) U = -(signedVol d P U) := by
-- proof
  simp only [signedVol, eval_neg, neg_pos, neg_lt_zero, neg_sub]

end PolynomialHamSandwich

namespace PolynomialHamSandwich

/--
[bisects_of_signedVol_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/PolynomialHamSandwich.lean)
-/
@[path]
lemma bisects_of_signedVol_zero
  {d : ℕ}
  {P : MvPolynomial (Fin d) ℝ}
  {U : Set (Fin d → ℝ)}
-- given
  (hU_bounded : Bornology.IsBounded U)
  (h : signedVol d P U = 0) :
-- imply
  Bisects d P U := by
-- proof
  unfold Bisects signedVol at *
  have hfp : volume ({x ∈ U | eval x P > 0}) ≠ ⊤ :=
    (Bornology.IsBounded.measure_lt_top (μ := volume)
      (hU_bounded.subset (Set.sep_subset U _))).ne
  have hfn : volume ({x ∈ U | eval x P < 0}) ≠ ⊤ :=
    (Bornology.IsBounded.measure_lt_top (μ := volume)
      (hU_bounded.subset (Set.sep_subset U _))).ne
  exact (ENNReal.toReal_eq_toReal_iff' hfp hfn).mp (by linarith)

end PolynomialHamSandwich

namespace PolynomialHamSandwich

/--
[combo_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/PolynomialHamSandwich.lean)
-/
@[path]
lemma combo_ne_zero
  {d m : ℕ}
  {basis : Fin m → MvPolynomial (Fin d) ℝ}
  {v : Fin m → ℝ}
-- given
  (hbasis : LinearIndependent ℝ basis)
  (hv : v ≠ 0) :
-- imply
  ∑ i, v i • basis i ≠ 0 := by
-- proof
  intro h; rw [linearIndependent_iff'] at hbasis
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra hall; push Not at hall; exact hv (funext hall)
  exact hj (hbasis Finset.univ v h j (Finset.mem_univ j))

end PolynomialHamSandwich

namespace PolynomialHamSandwich

/--
[combo_totalDegree_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/PolynomialHamSandwich.lean)
-/
@[path]
lemma combo_totalDegree_le
  {d D m : ℕ}
  {basis : Fin m → MvPolynomial (Fin d) ℝ}
  {v : Fin m → ℝ}
-- given
  (hbasis_deg : ∀ i, (basis i).totalDegree ≤ D) :
-- imply
  (∑ i, v i • basis i).totalDegree ≤ D :=
-- proof
  le_trans (totalDegree_finset_sum _ _)
    (Finset.sup_le (fun i _ => le_trans (totalDegree_smul_le _ _) (hbasis_deg i)))

end PolynomialHamSandwich

namespace PolynomialHamSandwich

/--
[sphere_vec_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/PolynomialHamSandwich.lean)
-/
@[path]
lemma sphere_vec_ne_zero
  {n : ℕ}
  {x : ↥(BorsukUlam.Sphere n)} :
-- imply
  (fun i => (x : EuclideanSpace ℝ (Fin (n + 1))) i) ≠ 0 := by
-- proof
  intro h
  have hx := x.property
  simp only [BorsukUlam.Sphere, Metric.mem_sphere, dist_zero_right] at hx
  have : (x : EuclideanSpace ℝ (Fin (n + 1))) = 0 := by ext i; exact congr_fun h i
  rw [this, norm_zero] at hx; exact one_ne_zero hx.symm
/-- The space of polynomials in `d` variables of total degree at most `D` has
dimension `binom(D + d, d)`; in particular it admits a linearly independent
family of that size all of whose elements have total degree `≤ D`. -/

end PolynomialHamSandwich


-- created on 2026-10-23
