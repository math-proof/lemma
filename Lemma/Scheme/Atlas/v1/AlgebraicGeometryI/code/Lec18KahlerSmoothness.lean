import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec18KahlerSmoothness.Part3
open IsLocalRing


/--
[Lemma30_cotangentSpace_dim_ge_krullDim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec18KahlerSmoothness.lean)
-/
@[path]
lemma Lemma30_cotangentSpace_dim_ge_krullDim
  {R : Type*}
  [CommRing R]
  [IsLocalRing R]
  [IsNoetherianRing R] :
-- imply
  ringKrullDim R ≤ Module.finrank (ResidueField R) (CotangentSpace R) := by
-- proof
  rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  exact ringKrullDim_le_spanFinrank_maximalIdeal R

/--
[Definition36_smooth_iff_regular](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec18KahlerSmoothness.lean)
-/
@[path]
lemma Definition36_smooth_iff_regular
  {R : Type*}
  [CommRing R]
  [IsLocalRing R]
  [IsNoetherianRing R] :
-- imply
  IsRegularLocalRing R ↔ Module.finrank (ResidueField R) (CotangentSpace R) = ringKrullDim R :=
-- proof
  IsRegularLocalRing.iff_finrank_cotangentSpace R

/--
[genericPoint_isRegularLocalRing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec18KahlerSmoothness.lean)
-/
@[path]
lemma genericPoint_isRegularLocalRing
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [Algebra k A]
  [Algebra.FiniteType k A] :
-- imply
  IsRegularLocalRing (Localization.AtPrime (⊥ : Ideal A)) := by
-- proof
  have hField : IsField (Localization.AtPrime (⊥ : Ideal A)) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq]
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    simp
  letI : Field (Localization.AtPrime (⊥ : Ideal A)) := hField.toField
  infer_instance

/--
[matrix_fin1_rank_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec18KahlerSmoothness.lean)
-/
@[path]
lemma matrix_fin1_rank_eq_zero_iff
  [Field k]
  {n : ℕ}
  {M : Matrix (Fin 1) (Fin n) k} :
-- imply
  M.rank = 0 ↔ M = 0 := by
-- proof
  unfold Matrix.rank
  constructor
  · intro h
    rw [Submodule.finrank_eq_zero] at h
    rw [LinearMap.range_eq_bot] at h
    ext i j
    have hcol := LinearMap.ext_iff.mp h (Pi.single j 1)
    simp [Matrix.mulVecLin, Matrix.mulVec_single] at hcol
    have : M.col j 0 = 0 := by rw [hcol]; rfl
    simp [Matrix.col] at this
    fin_cases i
    exact this
  · intro h
    subst h
    exact Matrix.rank_zero

/--
[matrix_fin1_rank_eq_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec18KahlerSmoothness.lean)
-/
@[path]
lemma matrix_fin1_rank_eq_one_iff
  [Field k]
  {n : ℕ}
  {M : Matrix (Fin 1) (Fin n) k} :
-- imply
  M.rank = 1 ↔ ∃ j, M 0 j ≠ 0 := by
-- proof
  have hle : M.rank ≤ 1 := by
    have := Matrix.rank_le_card_height M; simp at this; exact this
  constructor
  · intro h
    by_contra hall
    push Not at hall
    have hzero : M = 0 := by ext i j; fin_cases i; exact hall j
    rw [hzero, Matrix.rank_zero] at h; omega
  · intro ⟨j, hj⟩
    have hne : M ≠ 0 := by intro h; rw [h] at hj; simp at hj
    have hpos : 0 < M.rank := by
      by_contra h
      push Not at h
      exact hne ((matrix_fin1_rank_eq_zero_iff M).mp (by omega))
    omega

/--
[Corollary23_hypersurface_criterion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec18KahlerSmoothness.lean)
-/
@[path]
lemma Corollary23_hypersurface_criterion
  [Field k]
  {n : ℕ}
  {P : MvPolynomial (Fin n) k}
  {x : Fin n → k}
-- given
  (_hx : MvPolynomial.eval x P = 0) :
-- imply
  (∃ i : Fin n, MvPolynomial.eval x (MvPolynomial.pderiv i P) ≠ 0) ↔ (jacobianMatrix (fun _ : Fin 1 => P) x).rank = 1 := by
-- proof
  rw [matrix_fin1_rank_eq_one_iff]
  simp [jacobianMatrix]

/--
[span_range_le_maxIdealOfPoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec18KahlerSmoothness.lean)
-/
@[path]
lemma span_range_le_maxIdealOfPoint
  [Field k]
  {n m : ℕ}
  {f : Fin m → MvPolynomial (Fin n) k}
  {x : Fin n → k}
-- given
  (hx : ∀ i, MvPolynomial.eval x (f i) = 0) :
-- imply
  Ideal.span (Set.range f) ≤ maxIdealOfPoint x := by
-- proof
  rw [Ideal.span_le]
  intro p hp
  obtain ⟨i, rfl⟩ := hp
  rw [maxIdealOfPoint, SetLike.mem_coe, RingHom.mem_ker]
  exact hx i

/--
[eval_eq_zero_of_mem_le_maxIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec18KahlerSmoothness.lean)
-/
@[path]
lemma eval_eq_zero_of_mem_le_maxIdeal
  [Field k]
  {n m : ℕ}
  {I : Ideal (MvPolynomial (Fin n) k)}
  {x : Fin n → k}
  {f : Fin m → MvPolynomial (Fin n) k}
-- given
  (hI : I ≤ maxIdealOfPoint x)
  (hfI : ∀ i, f i ∈ I) :
-- imply
  ∀ i, MvPolynomial.eval x (f i) = 0 := by
-- proof
  intro i
  have h := hI (hfI i)
  rwa [maxIdealOfPoint, RingHom.mem_ker] at h
/-- Proposition 31 (Lecture 18). Smoothness of `V(I)` at `x` is equivalent to the existence
of polynomials `f_1,…,f_m ∈ I` with linearly independent Jacobian rows at `x` whose span,
after inverting some `u(x) ≠ 0`, equals `I` locally. -/


-- created on 2026-10-23
