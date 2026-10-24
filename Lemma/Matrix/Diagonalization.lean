import Mathlib
import sympy.Basic


namespace MathlibExt.LinearAlgebra.DiagonalizationWanted

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
/--
[diagonalization_iSup_ker_aeval_eq_ker_prod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Diagonalization.lean)
-/
@[path]
omit [FiniteDimensional K V] in
private lemma diagonalization_iSup_ker_aeval_eq_ker_prod
  (f : Module.End K V) (s : Finset K) :
  (⨆ μ ∈ s, LinearMap.ker (Polynomial.aeval f (Polynomial.X - Polynomial.C μ))) =
    LinearMap.ker (Polynomial.aeval f (∏ μ ∈ s, (Polynomial.X - Polynomial.C μ))) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.notMem_empty, Polynomial.aeval_sub, Polynomial.aeval_X,
      Polynomial.aeval_C, not_false_eq_true, iSup_neg, iSup_bot, Finset.prod_empty, map_one]
    rw [show (1 : Module.End K V) = LinearMap.id from rfl, LinearMap.ker_id]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.iSup_insert, ih]
    apply Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime
    refine IsCoprime.prod_right fun b hb ↦ ?_
    exact Polynomial.pairwise_coprime_X_sub_C Function.injective_id
      (ne_of_mem_of_not_mem hb ha).symm

end MathlibExt.LinearAlgebra.DiagonalizationWanted

namespace MathlibExt.LinearAlgebra.DiagonalizationWanted

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
/--
[diagonalization_roots_nodup_of_squarefree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Diagonalization.lean)
-/
@[path]
private lemma diagonalization_roots_nodup_of_squarefree
  (p : Polynomial K) (hp : Squarefree p) : p.roots.Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  intro a
  rw [p.count_roots]
  by_contra h
  have htwo : 2 ≤ p.rootMultiplicity a := by omega
  have hdvd : (Polynomial.X - Polynomial.C a) ^ 2 ∣ p :=
    (Polynomial.le_rootMultiplicity_iff hp.ne_zero).mp htwo
  exact Polynomial.not_isUnit_X_sub_C a (hp _ (by simpa [pow_two] using hdvd))

end MathlibExt.LinearAlgebra.DiagonalizationWanted

namespace MathlibExt.LinearAlgebra.DiagonalizationWanted

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
/--
[diagonalization_iSup_eigenspace_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Diagonalization.lean)
-/
@[path]
private lemma diagonalization_iSup_eigenspace_eq_top
  (f : Module.End K V) (hs : f.IsSemisimple) (h : f.charpoly.Splits) :
  ⨆ μ : K, f.eigenspace μ = ⊤ := by
  classical
  let p := minpoly K f
  have hpmonic : p.Monic := minpoly.monic (LinearMap.isIntegral f)
  have hpsplit : p.Splits := h.of_dvd (LinearMap.charpoly_monic f).ne_zero
    (LinearMap.minpoly_dvd_charpoly f)
  have hpnodup : p.roots.Nodup :=
    diagonalization_roots_nodup_of_squarefree p hs.minpoly_squarefree
  have hprod : (∏ μ ∈ p.roots.toFinset, (Polynomial.X - Polynomial.C μ)) = p := by
    rw [← Multiset.toFinset_eq hpnodup, Finset.prod_mk]
    exact (hpsplit.eq_prod_roots_of_monic hpmonic).symm
  have hkernels := diagonalization_iSup_ker_aeval_eq_ker_prod f p.roots.toFinset
  rw [hprod, minpoly.aeval K f, LinearMap.ker_zero] at hkernels
  have heigenspaces : (⨆ μ ∈ p.roots.toFinset, f.eigenspace μ) = ⊤ := by
    simpa only [Module.End.eigenspace_def, Polynomial.aeval_sub, Polynomial.aeval_X,
      Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one] using hkernels
  apply top_unique
  calc
    ⊤ = ⨆ μ ∈ p.roots.toFinset, f.eigenspace μ := heigenspaces.symm
    _ ≤ ⨆ μ : K, f.eigenspace μ := iSup_le fun μ ↦ iSup_le fun _ ↦ le_iSup _ μ

end MathlibExt.LinearAlgebra.DiagonalizationWanted

namespace MathlibExt.LinearAlgebra.DiagonalizationWanted

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
/--
[diagonalization_eigenbasis](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Diagonalization.lean)
-/
@[path]
private lemma diagonalization_eigenbasis
  {ι : Type*} [Fintype ι]
  (f : Module.End K V) (hs : f.IsSemisimple) (h : f.charpoly.Splits)
  (hdim : Module.finrank K V = Fintype.card ι) :
  ∃ (b : Module.Basis ι K V) (μ : ι → K), ∀ i, f.HasEigenvector (μ i) (b i) := by
  classical
  let hInternal : DirectSum.IsInternal f.eigenspace :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (Module.End.eigenspaces_iSupIndep f)
      (diagonalization_iSup_eigenspace_eq_top f hs h)
  let v := fun μ : K ↦ Module.Free.chooseBasis K (f.eigenspace μ)
  let b₀ := hInternal.collectedBasis v
  let _ : Finite (Σ μ, Module.Free.ChooseBasisIndex K (f.eigenspace μ)) :=
    Module.Finite.finite_basis b₀
  let _ : Fintype (Σ μ, Module.Free.ChooseBasisIndex K (f.eigenspace μ)) :=
    Fintype.ofFinite _
  let e : (Σ μ, Module.Free.ChooseBasisIndex K (f.eigenspace μ)) ≃ ι :=
    Fintype.equivOfCardEq (by rw [← Module.finrank_eq_card_basis b₀, hdim])
  refine ⟨b₀.reindex e, fun i ↦ (e.symm i).1, fun i ↦ ?_⟩
  rw [Module.End.hasEigenvector_iff, Module.Basis.reindex_apply]
  exact ⟨hInternal.collectedBasis_mem v (e.symm i), b₀.ne_zero _⟩

end MathlibExt.LinearAlgebra.DiagonalizationWanted

namespace MathlibExt.LinearAlgebra.DiagonalizationWanted

/--
[exists_eigenbasis_of_isSemisimple_of_splits](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Diagonalization.lean)
-/
@[path]
lemma exists_eigenbasis_of_isSemisimple_of_splits
  [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype ι] [DecidableEq ι]
  {f : Module.End K V}
-- given
  (hs : f.IsSemisimple)
  (h : f.charpoly.Splits)
  (hdim : Module.finrank K V = Fintype.card ι) :
-- imply
  ∃ (b : Module.Basis ι K V) (μ : ι → K), ∀ i, f.HasEigenvector (μ i) (b i) :=
-- proof
diagonalization_eigenbasis f hs h hdim

end MathlibExt.LinearAlgebra.DiagonalizationWanted

namespace MathlibExt.LinearAlgebra.DiagonalizationWanted

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
/--
[diagonalization_toMatrix_eq_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Diagonalization.lean)
-/
@[path]
omit [FiniteDimensional K V] in
private lemma diagonalization_toMatrix_eq_diagonal
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (f : Module.End K V) (b : Module.Basis ι K V) (μ : ι → K)
  (heigen : ∀ i, f.HasEigenvector (μ i) (b i)) :
  LinearMap.toMatrix b b f = Matrix.diagonal μ := by
  ext i j
  rw [LinearMap.toMatrix_apply, (heigen j).apply_eq_smul, map_smul, Module.Basis.repr_self,
    Finsupp.smul_single, smul_eq_mul, mul_one]
  by_cases hij : i = j
  · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
  · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]

end MathlibExt.LinearAlgebra.DiagonalizationWanted

namespace MathlibExt.LinearAlgebra.DiagonalizationWanted

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
/--
[diagonalization_exists_diagonal_similar](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Diagonalization.lean)
-/
@[path]
private lemma diagonalization_exists_diagonal_similar
  {n : Type*} [Fintype n] [DecidableEq n]
  (A : Matrix n n K) (hsplit : A.charpoly.Splits)
  (hsf : Squarefree (minpoly K (Matrix.toLin' A : Module.End K (n → K)))) :
  ∃ P D : Matrix n n K, D.IsDiag ∧ IsUnit P ∧ A = P * D * P⁻¹ := by
  let f : Module.End K (n → K) := Matrix.toLin' A
  have hsf' : Squarefree (minpoly K f) := by simpa [f] using hsf
  have hfss : f.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsf' (minpoly.aeval K f)
  have hfsplit : f.charpoly.Splits := by simpa [f] using hsplit
  obtain ⟨b, μ, heigen⟩ :=
    diagonalization_eigenbasis f hfss hfsplit (Module.finrank_pi (R := K))
  let e := Pi.basisFun K n
  have hPunit : IsUnit (e.toMatrix b) := by
    let _ := Module.Basis.invertibleToMatrix e b
    exact isUnit_of_invertible _
  refine ⟨e.toMatrix b, Matrix.diagonal μ, Matrix.isDiag_diagonal μ, hPunit, ?_⟩
  rw [Matrix.inv_eq_right_inv (Module.Basis.toMatrix_mul_toMatrix_flip e b)]
  rw [← diagonalization_toMatrix_eq_diagonal f b μ heigen]
  rw [basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
  simp [e, f]

end MathlibExt.LinearAlgebra.DiagonalizationWanted

namespace MathlibExt.LinearAlgebra.DiagonalizationWanted

/--
[exists_diagonal_similar_of_splits_of_squarefree_minpoly](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Diagonalization.lean)
-/
@[path]
lemma exists_diagonal_similar_of_splits_of_squarefree_minpoly
  [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype n] [DecidableEq n]
  {A : Matrix n n K}
-- given
  (hsplit : A.charpoly.Splits)
  (hsf : Squarefree (minpoly K (Matrix.toLin' A : Module.End K (n → K)))) :
-- imply
  ∃ P D : Matrix n n K, D.IsDiag ∧ IsUnit P ∧ A = P * D * P⁻¹ := by
-- proof
  exact diagonalization_exists_diagonal_similar A hsplit hsf

end MathlibExt.LinearAlgebra.DiagonalizationWanted


-- created on 2026-10-20
-- updated on 2026-10-23
