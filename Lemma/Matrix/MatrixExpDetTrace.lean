import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.LinearAlgebra.Matrix.MatrixExpDetTrace
open scoped BigOperators
open MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted


namespace MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

variable [Fintype n] [DecidableEq n]
/--
[matrixExp_exp_eq_sum_of_pow_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/MatrixExpDetTrace.lean)
-/
@[path]
private lemma matrixExp_exp_eq_sum_of_pow_eq_zero (A : Matrix n n ℂ) {m : ℕ}
  (hA : A ^ m = 0) :
  NormedSpace.exp A = ∑ k ∈ Finset.range m, (Nat.factorial k : ℂ)⁻¹ • A ^ k := by
  rw [NormedSpace.exp_eq_tsum ℂ]
  exact tsum_eq_sum fun k hk ↦ by
    have hmk : m ≤ k := Nat.le_of_not_gt fun hkm ↦ hk (Finset.mem_range.mpr hkm)
    rw [pow_eq_zero_of_le hmk hA, smul_zero]

end MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

namespace MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

variable [Fintype n] [DecidableEq n]
/--
[matrixExp_exp_pi_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/MatrixExpDetTrace.lean)
-/
@[path]
omit [Fintype n] [DecidableEq n] in
private lemma matrixExp_exp_pi_apply [Finite n] (v : n → ℂ) (i : n) :
  NormedSpace.exp v i = Complex.exp (v i) := by
  let _ := Fintype.ofFinite n
  simpa only [Pi.evalRingHom_apply, Complex.exp_eq_exp_ℂ] using
    (NormedSpace.map_exp (Pi.evalRingHom (fun _ : n ↦ ℂ) i) (continuous_apply i) v)

end MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

namespace MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

variable [Fintype n] [DecidableEq n]
/--
[matrixExp_det_exp_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/MatrixExpDetTrace.lean)
-/
@[path]
private lemma matrixExp_det_exp_diagonal (v : n → ℂ) :
  Matrix.det (NormedSpace.exp (Matrix.diagonal v)) =
    Complex.exp (Matrix.trace (Matrix.diagonal v)) := by
  rw [Matrix.exp_diagonal, Matrix.det_diagonal, Matrix.trace_diagonal, Complex.exp_sum]
  simp_rw [matrixExp_exp_pi_apply]

end MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

namespace MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

variable [Fintype n] [DecidableEq n]
/--
[matrixExp_dfinsupp_basis_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/MatrixExpDetTrace.lean)
-/
@[path]
omit [Fintype n] [DecidableEq n] in
private lemma matrixExp_dfinsupp_basis_apply
  {R ι : Type*} [Semiring R] [DecidableEq ι] {M : ι → Type*}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] {η : ι → Type*}
  (b : ∀ i, Module.Basis (η i) R (M i)) (i : Σ x, η x) :
  DFinsupp.basis b i = DFinsupp.single i.1 (b i.1 i.2) := by
  obtain ⟨x, i⟩ := i
  apply Module.Basis.apply_eq_iff.mpr
  ext ⟨y, j⟩
  by_cases hxy : x = y
  · subst y
    simp [DFinsupp.basis]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  · simp [DFinsupp.basis, hxy]

end MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

namespace MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

variable [Fintype n] [DecidableEq n]
/--
[matrixExp_eigenbasis_apply_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/MatrixExpDetTrace.lean)
-/
@[path]
omit [Fintype n] [DecidableEq n] in
private lemma matrixExp_eigenbasis_apply_mem {V : Type*} [AddCommGroup V] [Module ℂ V]
  (f : Module.End ℂ V) (h : ⨆ z, f.eigenspace z = ⊤)
  (i : Σ z, Module.Basis.ofVectorSpaceIndex ℂ (f.eigenspace z)) :
  matrixExp_eigenbasis f h i ∈ f.eigenspace i.1 := by
  classical
  rw [matrixExp_eigenbasis, Module.Basis.map_apply, matrixExp_dfinsupp_basis_apply,
    iSupIndep.linearEquiv_apply, DFinsupp.sumAddHom_single]
  exact (Module.Basis.ofVectorSpace ℂ (f.eigenspace i.1) i.2).property

end MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

namespace MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

variable [Fintype n] [DecidableEq n]
/--
[matrixExp_diagonalizingBasis_apply_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/MatrixExpDetTrace.lean)
-/
@[path]
omit [Fintype n] [DecidableEq n] in
private lemma matrixExp_diagonalizingBasis_apply_mem
  {V ι : Type*} [AddCommGroup V] [Module ℂ V] (b₀ : Module.Basis ι ℂ V)
  (f : Module.End ℂ V) (h : ⨆ z, f.eigenspace z = ⊤) (i : ι) :
  matrixExp_diagonalizingBasis b₀ f h i ∈
    f.eigenspace (matrixExp_diagonalizingEigenvalue b₀ f h i) := by
  rw [matrixExp_diagonalizingBasis, Module.Basis.reindex_apply]
  exact matrixExp_eigenbasis_apply_mem f h (b₀.indexEquiv (matrixExp_eigenbasis f h) i)

end MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

namespace MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

variable [Fintype n] [DecidableEq n]
/--
[matrixExp_toMatrix_diagonalizingBasis](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/MatrixExpDetTrace.lean)
-/
@[path]
omit [Fintype n] [DecidableEq n] in
private lemma matrixExp_toMatrix_diagonalizingBasis
  {V ι : Type*} [AddCommGroup V] [Module ℂ V] [Fintype ι] [DecidableEq ι]
  (b₀ : Module.Basis ι ℂ V) (f : Module.End ℂ V) (h : ⨆ z, f.eigenspace z = ⊤) :
  LinearMap.toMatrix (matrixExp_diagonalizingBasis b₀ f h)
    (matrixExp_diagonalizingBasis b₀ f h) f =
    Matrix.diagonal (matrixExp_diagonalizingEigenvalue b₀ f h) := by
  classical
  ext i j
  rw [LinearMap.toMatrix_apply,
    Module.End.mem_eigenspace_iff.mp (matrixExp_diagonalizingBasis_apply_mem b₀ f h j),
    map_smul, Module.Basis.repr_self]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

end MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

namespace MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

variable [Fintype n] [DecidableEq n]
/--
[matrixExp_changeBasis_exp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/MatrixExpDetTrace.lean)
-/
@[path]
open scoped Matrix.Norms.Operator in
private lemma matrixExp_changeBasis_exp (b : Module.Basis n ℂ (n → ℂ))
  (A : Matrix n n ℂ) :
  matrixExp_changeBasisAlgEquiv b (NormedSpace.exp A) =
    NormedSpace.exp (matrixExp_changeBasisAlgEquiv b A) := by
  let e := matrixExp_changeBasisAlgEquiv b
  let f : Matrix n n ℂ →+* Matrix n n ℂ := e.toRingEquiv.toRingHom
  have hc : Continuous f := by
    change Continuous e
    exact e.toLinearMap.continuous_of_finiteDimensional
  change f (NormedSpace.exp A) = NormedSpace.exp (f A)
  exact NormedSpace.map_exp f hc A

end MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

namespace MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

variable [Fintype n] [DecidableEq n]
/--
[matrixExp_det_changeBasis](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/MatrixExpDetTrace.lean)
-/
@[path]
private lemma matrixExp_det_changeBasis (b : Module.Basis n ℂ (n → ℂ))
  (A : Matrix n n ℂ) :
  Matrix.det (matrixExp_changeBasisAlgEquiv b A) = Matrix.det A := by
  change Matrix.det (LinearMap.toMatrix b b (Matrix.toLin' A)) = Matrix.det A
  rw [LinearMap.det_toMatrix]
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ n)]
  rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

end MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

namespace MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

variable [Fintype n] [DecidableEq n]
/--
[matrixExp_trace_changeBasis](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/MatrixExpDetTrace.lean)
-/
@[path]
private lemma matrixExp_trace_changeBasis (b : Module.Basis n ℂ (n → ℂ))
  (A : Matrix n n ℂ) :
  Matrix.trace (matrixExp_changeBasisAlgEquiv b A) = Matrix.trace A := by
  change Matrix.trace (LinearMap.toMatrix b b (Matrix.toLin' A)) = Matrix.trace A
  rw [← LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace_toLin'_eq]

end MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

namespace MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

variable [Fintype n] [DecidableEq n]
/--
[matrixExp_det_exp_of_isSemisimple](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/MatrixExpDetTrace.lean)
-/
@[path]
private lemma matrixExp_det_exp_of_isSemisimple (A : Matrix n n ℂ)
  (hA : Module.End.IsSemisimple (Matrix.toLin' A)) :
  Matrix.det (NormedSpace.exp A) = Complex.exp (Matrix.trace A) := by
  let f : Module.End ℂ (n → ℂ) := Matrix.toLin' A
  have htop : ⨆ z, f.eigenspace z = ⊤ := hA.iSup_eigenspace_eq_top
  let b₀ := Pi.basisFun ℂ n
  let b := matrixExp_diagonalizingBasis b₀ f htop
  let v := matrixExp_diagonalizingEigenvalue b₀ f htop
  have hdiag : matrixExp_changeBasisAlgEquiv b A = Matrix.diagonal v := by
    exact matrixExp_toMatrix_diagonalizingBasis b₀ f htop
  calc
    Matrix.det (NormedSpace.exp A) =
      Matrix.det (matrixExp_changeBasisAlgEquiv b (NormedSpace.exp A)) :=
      (matrixExp_det_changeBasis b (NormedSpace.exp A)).symm
    _ = Matrix.det (NormedSpace.exp (matrixExp_changeBasisAlgEquiv b A)) := by
      rw [matrixExp_changeBasis_exp]
    _ = Matrix.det (NormedSpace.exp (Matrix.diagonal v)) := by rw [hdiag]
    _ = Complex.exp (Matrix.trace (Matrix.diagonal v)) := matrixExp_det_exp_diagonal v
    _ = Complex.exp (Matrix.trace (matrixExp_changeBasisAlgEquiv b A)) := by rw [hdiag]
    _ = Complex.exp (Matrix.trace A) := by rw [matrixExp_trace_changeBasis]

end MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

namespace MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

variable [Fintype n] [DecidableEq n]
/--
[matrixExp_det_one_add_of_isNilpotent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/MatrixExpDetTrace.lean)
-/
@[path]
private lemma matrixExp_det_one_add_of_isNilpotent (A : Matrix n n ℂ)
  (hA : IsNilpotent A) : Matrix.det (1 + A) = 1 := by
  obtain ⟨r, -, hchar⟩ := Polynomial.isUnit_iff.mp
    (Matrix.isUnit_charpolyRev_of_isNilpotent hA)
  have hr : r = 1 := by
    simpa using congrArg (Polynomial.eval 0) hchar
  have hchar' : A.charpolyRev = 1 := by rw [← hchar, hr, map_one]
  have heval := congrArg (Polynomial.eval (-1)) hchar'
  have hdiag : Matrix.diagonal (fun _ : n ↦ (-1 : ℂ)) = -1 := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  simpa [Matrix.charpolyRev, eval_det, hdiag] using heval

end MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

namespace MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

variable [Fintype n] [DecidableEq n]
/--
[matrixExp_normed_exp_eq_nilpotent_exp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/MatrixExpDetTrace.lean)
-/
@[path]
private lemma matrixExp_normed_exp_eq_nilpotent_exp (A : Matrix n n ℂ)
  (hA : IsNilpotent A) : NormedSpace.exp A = IsNilpotent.exp A := by
  obtain ⟨m, hm⟩ := hA
  rw [matrixExp_exp_eq_sum_of_pow_eq_zero A hm, IsNilpotent.exp_eq_sum hm]
  apply Finset.sum_congr rfl
  intro k _
  simpa using (ratCast_smul_eq ℂ ℚ ((k.factorial : ℚ)⁻¹) (A ^ k))

end MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

namespace MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

variable [Fintype n] [DecidableEq n]
/--
[matrixExp_det_exp_of_isNilpotent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/MatrixExpDetTrace.lean)
-/
@[path]
private lemma matrixExp_det_exp_of_isNilpotent (A : Matrix n n ℂ)
  (hA : IsNilpotent A) : Matrix.det (NormedSpace.exp A) = 1 := by
  have h : IsNilpotent (NormedSpace.exp A - 1) := by
    rwa [matrixExp_normed_exp_eq_nilpotent_exp A hA]
  simpa using matrixExp_det_one_add_of_isNilpotent (NormedSpace.exp A - 1) h

end MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

namespace MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

variable [Fintype n] [DecidableEq n]
/--
[matrixExp_exists_isNilpotent_isSemisimple](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/MatrixExpDetTrace.lean)
-/
@[path]
private lemma matrixExp_exists_isNilpotent_isSemisimple (A : Matrix n n ℂ) :
  ∃ N S : Matrix n n ℂ, IsNilpotent N ∧
    Module.End.IsSemisimple (Matrix.toLin' S) ∧ Commute N S ∧ A = N + S := by
  let f : Module.End ℂ (n → ℂ) := Matrix.toLin' A
  obtain ⟨N, hNmem, S, hSmem, hN, hS, hdecomp⟩ :=
    Module.End.exists_isNilpotent_isSemisimple (f := f)
  let e : Module.End ℂ (n → ℂ) ≃ₐ[ℂ] Matrix n n ℂ :=
    LinearMap.toMatrixAlgEquiv (Pi.basisFun ℂ n)
  have he (g : Module.End ℂ (n → ℂ)) : e g = LinearMap.toMatrix' g := by
    change LinearMap.toMatrix (Pi.basisFun ℂ n) (Pi.basisFun ℂ n) g = _
    rw [LinearMap.toMatrix_eq_toMatrix']
  have hNS : Commute N S :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hSmem
      (Algebra.commute_of_mem_adjoin_self hNmem).symm
  refine ⟨e N, e S, hN.map e, ?_, hNS.map e, ?_⟩
  · rw [he, Matrix.toLin'_toMatrix']
    exact hS
  · rw [he, he]
    have h := congrArg LinearMap.toMatrix' hdecomp
    simpa [f] using h

end MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

namespace MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

/--
[matrix_det_exp_eq_exp_trace](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/MatrixExpDetTrace.lean)
-/
@[path]
lemma matrix_det_exp_eq_exp_trace
  [Fintype n] [DecidableEq n]
  {A : Matrix n n ℂ} :
-- imply
  Matrix.det (NormedSpace.exp A) = Complex.exp (Matrix.trace A) := by
-- proof
  obtain ⟨N, S, hN, hS, hNS, rfl⟩ := matrixExp_exists_isNilpotent_isSemisimple A
  have htraceN : Matrix.trace N = 0 :=
    (Matrix.isNilpotent_trace_of_isNilpotent hN).eq_zero
  rw [Matrix.exp_add_of_commute N S hNS, Matrix.det_mul,
    matrixExp_det_exp_of_isNilpotent N hN, matrixExp_det_exp_of_isSemisimple S hS,
    Matrix.trace_add, htraceN, zero_add, one_mul]

end MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

namespace MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

/--
[matrix_exp_eq_sum_of_isNilpotent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/MatrixExpDetTrace.lean)
-/
@[path]
lemma matrix_exp_eq_sum_of_isNilpotent
  [Fintype n] [DecidableEq n]
  {A : Matrix n n ℂ}
-- given
  (h : IsNilpotent A) :
-- imply
  ∃ m : ℕ, NormedSpace.exp A = ∑ k ∈ Finset.range m, (Nat.factorial k : ℂ)⁻¹ • A ^ k := by
-- proof
  obtain ⟨m, hm⟩ := h
  exact ⟨m, matrixExp_exp_eq_sum_of_pow_eq_zero A hm⟩

end MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted


-- created on 2026-10-20
-- updated on 2026-10-26
