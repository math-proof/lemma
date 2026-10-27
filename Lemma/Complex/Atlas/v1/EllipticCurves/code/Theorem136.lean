import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.EllipticCurves.code.Theorem136.Part4
open Module Polynomial EllipticCurve EndomorphismRingOverFiniteField
open scoped TensorProduct


namespace EllipticCurve

/--
[endPoly_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem136.lean)
-/
@[path]
lemma endPoly_natDegree
  {F : Type u}
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {W : WeierstrassCurve.Affine F} :
-- imply
  (endPoly W).natDegree = 2 := by
-- proof
  unfold endPoly; simp

end EllipticCurve

namespace EllipticCurve

/--
[EndAlgebra.sqrtD_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem136.lean)
-/
@[path]
lemma EndAlgebra.sqrtD_sq
  {F : Type u}
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {W : WeierstrassCurve.Affine F} :
-- imply
  EndAlgebra.sqrtD W ^ 2 = algebraMap ℚ (EndAlgebra W) (frobeniusDiscriminantQ W) := by
-- proof
  have h := AdjoinRoot.eval₂_root (endPoly W)
  change Polynomial.eval₂ (AdjoinRoot.of (endPoly W))
    (AdjoinRoot.root (endPoly W)) (endPoly W) = 0 at h
  unfold endPoly at h
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  exact sub_eq_zero.mp h
end EllipticCurve


namespace EndomorphismRingOverFiniteField

/--
[frobeniusDiscriminant_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem136.lean)
-/
@[path]
lemma frobeniusDiscriminant_def
  {F : Type u}
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {W : WeierstrassCurve.Affine F} :
-- imply
  frobeniusDiscriminant W = (Hasse.traceFrobenius W) ^ 2 - 4 * (Fintype.card F : ℤ) :=
-- proof
  rfl

end EndomorphismRingOverFiniteField

namespace EndomorphismRingOverFiniteField

/--
[frobeniusDiscriminant_eq_Q](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem136.lean)
-/
@[path]
lemma frobeniusDiscriminant_eq_Q
  {F : Type u}
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {W : WeierstrassCurve.Affine F} :
-- imply
  (frobeniusDiscriminant W : ℚ) = EllipticCurve.frobeniusDiscriminantQ W := by
-- proof
  simp [frobeniusDiscriminant, EllipticCurve.frobeniusDiscriminantQ]

end EndomorphismRingOverFiniteField

namespace EndomorphismRingOverFiniteField

/--
[frobeniusDiscriminant_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem136.lean)
-/
@[path]
lemma frobeniusDiscriminant_nonpos
  {F : Type u}
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {W : WeierstrassCurve.Affine F}
-- given
  (hq : 0 < Fintype.card F) :
-- imply
  frobeniusDiscriminant W ≤ 0 := by
-- proof
  simp only [frobeniusDiscriminant_def]
  have hsq := Hasse.trace_sq_le_four_mul_card W hq
  have : (Hasse.traceFrobenius W : ℝ) ^ 2 = ((Hasse.traceFrobenius W ^ 2 : ℤ) : ℝ) := by push_cast; ring
  rw [this] at hsq
  have h4q : (4 * (Fintype.card F : ℝ)) = ((4 * (Fintype.card F : ℤ) : ℤ) : ℝ) := by push_cast; ring
  rw [h4q] at hsq
  have : Hasse.traceFrobenius W ^ 2 ≤ 4 * (Fintype.card F : ℤ) := by exact_mod_cast hsq
  linarith

end EndomorphismRingOverFiniteField

namespace EndomorphismRingOverFiniteField

/--
[frobeniusDiscriminant_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem136.lean)
-/
@[path]
lemma frobeniusDiscriminant_neg
  {F : Type u}
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {W : WeierstrassCurve.Affine F}
-- given
  (hq : 0 < Fintype.card F)
  (hnotint : frobeniusNotInt W) :
-- imply
  frobeniusDiscriminant W < 0 := by
-- proof
  have hle := frobeniusDiscriminant_nonpos W hq
  have hne : frobeniusDiscriminant W ≠ 0 := by
    simp only [frobeniusDiscriminant_def, frobeniusNotInt] at hnotint ⊢
    omega
  omega

end EndomorphismRingOverFiniteField

namespace EndomorphismRingOverFiniteField

/--
[frobeniusDiscriminantQ_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem136.lean)
-/
@[path]
lemma frobeniusDiscriminantQ_neg
  {F : Type u}
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {W : WeierstrassCurve.Affine F}
-- given
  (hq : 0 < Fintype.card F)
  (hnotint : frobeniusNotInt W) :
-- imply
  EllipticCurve.frobeniusDiscriminantQ W < 0 := by
-- proof
  have h := frobeniusDiscriminant_neg W hq hnotint
  rw [← frobeniusDiscriminant_eq_Q]
  exact_mod_cast h

end EndomorphismRingOverFiniteField

namespace EndomorphismRingOverFiniteField

/--
[endAlg_finrank_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem136.lean)
-/
@[path]
lemma endAlg_finrank_eq_two
  {F : Type u}
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {E : WeierstrassCurve.Affine F}
-- given
  (hq : 0 < Fintype.card F)
  (hnotint : frobeniusNotInt E) :
-- imply
  Module.finrank ℚ (EllipticCurve.EndAlgebra E) = 2 := by
-- proof
  show Module.finrank ℚ (AdjoinRoot (EllipticCurve.endPoly E)) = 2
  have hne := EllipticCurve.endPoly_ne_zero E
  rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim hne]
  exact EllipticCurve.endPoly_natDegree E

end EndomorphismRingOverFiniteField

namespace EndomorphismRingOverFiniteField

/--
[endAlg_has_imaginary_generator](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem136.lean)
-/
@[path]
lemma endAlg_has_imaginary_generator
  {F : Type u}
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {E : WeierstrassCurve.Affine F}
-- given
  (hq : 0 < Fintype.card F)
  (hnotint : frobeniusNotInt E) :
-- imply
  ∃ α : EllipticCurve.EndAlgebra E, (∀ q : ℚ, α ≠ (algebraMap ℚ (EllipticCurve.EndAlgebra E)) q) ∧ ∃ d : ℚ, d < 0 ∧ α * α = (algebraMap ℚ (EllipticCurve.EndAlgebra E)) d := by
-- proof
  refine ⟨EllipticCurve.EndAlgebra.sqrtD E, ?_, ?_⟩
  ·
    intro q hq_eq
    have hD_neg := frobeniusDiscriminantQ_neg E hq hnotint
    have hinj : Function.Injective (algebraMap ℚ (EllipticCurve.EndAlgebra E)) :=
      (algebraMap ℚ (EllipticCurve.EndAlgebra E)).injective
    have hsq := EllipticCurve.EndAlgebra.sqrtD_sq E
    rw [hq_eq, ← map_pow] at hsq
    have := hinj hsq
    linarith [sq_nonneg q]
  ·
    refine ⟨EllipticCurve.frobeniusDiscriminantQ E,
      frobeniusDiscriminantQ_neg E hq hnotint, ?_⟩
    rw [← sq]
    exact EllipticCurve.EndAlgebra.sqrtD_sq E
/-- The abstract endomorphism algebra of $E$ is ring-isomorphic to
$\mathbb{Q}[X]/(X^2 - \Delta_\pi)$ (part of Theorem 13.6: identifies $\mathrm{End}^0(E)$
with $\mathbb{Q}(\sqrt{\Delta_\pi})$). -/

end EndomorphismRingOverFiniteField

/--
[endPoly_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem136.lean)
-/
@[path]
private lemma endPoly_ne_zero_eq
  {F : Type u}
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {W : WeierstrassCurve.Affine F} :
-- imply
  endPoly W ≠ 0 := by
-- proof
  apply EllipticCurve.endPoly_ne_zero W

/--
[endPoly_degree_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem136.lean)
-/
@[path]
private lemma endPoly_degree_ne_zero_eq
  {F : Type u}
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {W : WeierstrassCurve.Affine F} :
-- imply
  (endPoly W).degree ≠ 0 := by
-- proof
  apply EllipticCurve.endPoly_degree_ne_zero W


-- created on 2026-10-23
