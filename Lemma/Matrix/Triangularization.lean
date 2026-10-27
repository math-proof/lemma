import Mathlib
import Initialize.Tactic.Attr.Basic
open Polynomial


namespace MathlibExt.LinearAlgebra.TriangularizationWanted

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
/--
[triangularization_aeval_mapQ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Triangularization.lean)
-/
@[path]
omit [FiniteDimensional K V] in
private lemma triangularization_aeval_mapQ
  (W : Submodule K V) (f : Module.End K V) (hf : W ≤ W.comap f) (p : K[X]) :
  aeval (W.mapQ W f hf) p =
    W.mapQ W (aeval f p)
      (fun _x hx => aeval_apply_smul_mem_of_le_comap hx p f hf) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    apply W.quot_hom_ext
    intro x
    simp only [map_add, LinearMap.add_apply, hp, hq, Submodule.mapQ_apply]
    rfl
  | monomial n a =>
    apply W.quot_hom_ext
    intro x
    simp only [Polynomial.aeval_monomial, Module.algebraMap_end_apply,
      Module.End.mul_apply, Submodule.mapQ_apply]
    rw [← W.mapQ_pow hf n]
    rfl

end MathlibExt.LinearAlgebra.TriangularizationWanted

namespace MathlibExt.LinearAlgebra.TriangularizationWanted

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
/--
[triangularization_minpoly_mapQ_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Triangularization.lean)
-/
@[path]
omit [FiniteDimensional K V] in
private lemma triangularization_minpoly_mapQ_dvd
  (W : Submodule K V) (f : Module.End K V) (hf : W ≤ W.comap f) :
  minpoly K (W.mapQ W f hf) ∣ minpoly K f := by
  apply minpoly.dvd
  rw [triangularization_aeval_mapQ]
  apply W.quot_hom_ext
  intro x
  simp only [Submodule.mapQ_apply, LinearMap.zero_apply]
  rw [minpoly.aeval]
  rfl

end MathlibExt.LinearAlgebra.TriangularizationWanted

namespace MathlibExt.LinearAlgebra.TriangularizationWanted

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
/--
[triangularization_exists_eigenvalue_of_minpoly_splits](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Triangularization.lean)
-/
@[path]
private lemma triangularization_exists_eigenvalue_of_minpoly_splits
  [Nontrivial V] (f : Module.End K V) (h : (minpoly K f).Splits) :
  ∃ μ : K, f.HasEigenvalue μ := by
  have hint : IsIntegral K f := LinearMap.isIntegral f
  obtain ⟨μ, hμ⟩ := h.exists_eval_eq_zero (ne_of_gt (minpoly.degree_pos hint))
  exact ⟨μ, Module.End.hasEigenvalue_of_isRoot hμ⟩

end MathlibExt.LinearAlgebra.TriangularizationWanted

namespace MathlibExt.LinearAlgebra.TriangularizationWanted

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
/--
[triangularization_exists_basis_fin](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Triangularization.lean)
-/
@[path]
private lemma triangularization_exists_basis_fin
  {n : ℕ} (f : Module.End K V) (h : (minpoly K f).Splits)
  (hdim : Module.finrank K V = n) :
  ∃ b : Module.Basis (Fin n) K V,
    (LinearMap.toMatrix b b f).IsUpperTriangular := by
  induction n generalizing V with
  | zero =>
    let b := Module.finBasisOfFinrankEq K V hdim
    refine ⟨b, ?_⟩
    intro i
    exact Fin.elim0 i
  | succ n ih =>
    have hfin : 0 < Module.finrank K V := by omega
    let nontrivialV : Nontrivial V := Module.finrank_pos_iff.mp hfin
    obtain ⟨μ, hμ⟩ :=
      @triangularization_exists_eigenvalue_of_minpoly_splits K V _ _ _ _ nontrivialV f h
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hμ
    have hfv : f v = μ • v := Module.End.mem_eigenspace_iff.mp hv
    let W : Submodule K V := K ∙ v
    have hfW : W ≤ W.comap f := by
      change K ∙ v ≤ (K ∙ v).comap f
      rw [Submodule.span_singleton_le_iff_mem]
      change f v ∈ K ∙ v
      rw [hfv]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    let fQ : Module.End K (V ⧸ W) := W.mapQ W f hfW
    have hQsplit : (minpoly K fQ).Splits := by
      apply h.of_dvd (minpoly.ne_zero (LinearMap.isIntegral f))
      exact triangularization_minpoly_mapQ_dvd W f hfW
    have hWdim : Module.finrank K W = 1 := by
      simpa only [W] using finrank_span_singleton hv0
    have hQdim : Module.finrank K (V ⧸ W) = n := by
      have hrank := W.finrank_quotient_add_finrank
      omega
    obtain ⟨bQ, hbQ⟩ := ih fQ hQsplit hQdim
    let bW : Module.Basis (Fin 1) K W := Module.finBasisOfFinrankEq K W hWdim
    let bS : Module.Basis (Fin 1 ⊕ Fin n) K V := bW.sumQuot bQ
    let e : (Fin 1 ⊕ Fin n) ≃ Fin (n + 1) :=
      finSumFinEquiv.trans (finCongr (Nat.add_comm 1 n))
    refine ⟨bS.reindex e, ?_⟩
    intro i j hji
    obtain ⟨i | i, rfl⟩ := e.surjective i
    · obtain ⟨j | j, rfl⟩ := e.surjective j
      · have : i = j := Subsingleton.elim _ _
        subst j
        exact (lt_irrefl _ hji).elim
      · change 1 + j.val < i.val at hji
        omega
    · obtain ⟨j | j, rfl⟩ := e.surjective j
      · simp only [LinearMap.toMatrix_apply, Module.Basis.reindex_apply,
        Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply]
        dsimp only [bS]
        rw [Module.Basis.sumQuot_inl]
        exact bW.sumQuot_repr_inr_of_mem bQ _ (hfW (bW j).property) i
      · have hji' : j < i := by
        change 1 + j.val < 1 + i.val at hji
        omega
        simp only [LinearMap.toMatrix_apply, Module.Basis.reindex_apply,
          Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply]
        dsimp only [bS]
        rw [Module.Basis.sumQuot_repr_inr, Submodule.mkQ_apply]
        have hmap :
          Submodule.Quotient.mk (f ((bW.sumQuot bQ) (Sum.inr j))) =
            fQ (Submodule.Quotient.mk ((bW.sumQuot bQ) (Sum.inr j))) := by
          simpa only [fQ] using
            (Submodule.mapQ_apply W W f ((bW.sumQuot bQ) (Sum.inr j))).symm
        rw [hmap, Module.Basis.sumQuot_inr]
        simpa only [LinearMap.toMatrix_apply] using hbQ hji'

end MathlibExt.LinearAlgebra.TriangularizationWanted

namespace MathlibExt.LinearAlgebra.TriangularizationWanted

/--
[exists_basis_upperTriangular_toMatrix](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Triangularization.lean)
-/
@[path]
lemma exists_basis_upperTriangular_toMatrix
  [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
  {f : Module.End K V}
-- given
  (h : f.charpoly.Splits)
  (hdim : Module.finrank K V = Fintype.card ι) :
-- imply
  ∃ b : Module.Basis ι K V, (LinearMap.toMatrix b b f).IsUpperTriangular := by
-- proof
  have hmin : (minpoly K f).Splits :=
    h.of_dvd (LinearMap.charpoly_monic f).ne_zero (LinearMap.minpoly_dvd_charpoly f)
  obtain ⟨b, hb⟩ := triangularization_exists_basis_fin f hmin hdim
  let e : Fin (Fintype.card ι) ≃o ι := Fintype.orderIsoFinOfCardEq ι rfl
  refine ⟨b.reindex e.toEquiv, ?_⟩
  intro i j hji
  rw [LinearMap.toMatrix_apply, Module.Basis.reindex_apply,
    Module.Basis.repr_reindex_apply]
  rw [← LinearMap.toMatrix_apply]
  exact hb (e.symm.lt_iff_lt.mpr hji)

end MathlibExt.LinearAlgebra.TriangularizationWanted

namespace MathlibExt.LinearAlgebra.TriangularizationWanted

/--
[exists_upperTriangular_similar_of_splits](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Triangularization.lean)
-/
@[path]
lemma exists_upperTriangular_similar_of_splits
  [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype n] [DecidableEq n] [LinearOrder n]
  {A : Matrix n n K}
-- given
  (h : A.charpoly.Splits) :
-- imply
  ∃ P T : Matrix n n K, IsUnit P ∧ T.IsUpperTriangular ∧ A = P * T * P⁻¹ := by
-- proof
  let e : Module.Basis n K (n → K) := Pi.basisFun K n
  let f : Module.End K (n → K) := Matrix.toLin e e A
  have hfchar : f.charpoly.Splits := by
    dsimp only [f]
    rwa [Matrix.charpoly_toLin A e]
  obtain ⟨b, hb⟩ := exists_basis_upperTriangular_toMatrix (ι := n) f hfchar (by simp)
  let P : Matrix n n K := e.toMatrix b
  let T : Matrix n n K := LinearMap.toMatrix b b f
  have hP : IsUnit P := by
    apply IsUnit.of_mul_eq_one (b.toMatrix e)
    dsimp only [P]
    exact Module.Basis.toMatrix_mul_toMatrix_flip e b
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPinv : b.toMatrix e = P⁻¹ := by
    calc
      b.toMatrix e = b.toMatrix e * 1 := (mul_one _).symm
      _ = b.toMatrix e * (P * P⁻¹) := by rw [Matrix.mul_nonsing_inv P hPdet]
      _ = (b.toMatrix e * P) * P⁻¹ := (Matrix.mul_assoc _ _ _).symm
      _ = P⁻¹ := by
        rw [show b.toMatrix e * P = 1 by
          dsimp only [P]
          exact Module.Basis.toMatrix_mul_toMatrix_flip b e, one_mul]
  have hchange : P * T * b.toMatrix e = A := by
    calc
      P * T * b.toMatrix e = LinearMap.toMatrix e e f := by
        dsimp only [P, T]
        exact basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix e b e b f
      _ = A := by
        dsimp only [f]
        exact LinearMap.toMatrix_toLin e e A
  refine ⟨P, T, hP, ?_, ?_⟩
  · exact hb
  · rw [← hPinv]
    exact hchange.symm

end MathlibExt.LinearAlgebra.TriangularizationWanted


-- created on 2026-10-20
-- updated on 2026-10-26
