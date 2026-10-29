import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped NumberField
open NumberField.InfinitePlace


namespace NumberField.Units

/--
[finiteIndex_closure_range_of_lt_one_off_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Units.lean)
-/
@[path]
lemma finiteIndex_closure_range_of_lt_one_off_diagonal
  [Field F] [NumberField F]
  {u : NumberField.InfinitePlace F → (𝓞 F)ˣ}
-- given
  (hu : ∀ v w : NumberField.InfinitePlace F, w ≠ v → w (u v) < 1) :
-- imply
  (Subgroup.closure (Set.range u)).FiniteIndex := by
-- proof
  classical
  let v : {w : NumberField.InfinitePlace F // w ≠ dirichletUnitTheorem.w₀} →
      dirichletUnitTheorem.logSpace F :=
    fun i => logEmbedding F (Additive.ofMul (u i.val))
  let B := Pi.basisFun ℝ
    {w : NumberField.InfinitePlace F // w ≠ dirichletUnitTheorem.w₀}
  have hneg : ∀ (k i : {w : NumberField.InfinitePlace F //
      w ≠ dirichletUnitTheorem.w₀}),
      i ∈ Finset.univ.erase k → (v k) i < 0 := by
    intro k i hi
    have hne : i.val ≠ k.val := fun h => Finset.ne_of_mem_erase hi (Subtype.ext h)
    have hcomp : (v k) i =
        ((mult i.val : ℝ) * Real.log (i.val (u k.val))) :=
      dirichletUnitTheorem.logEmbedding_component _ _
    rw [hcomp]
    refine mul_neg_of_pos_of_neg ?_
      (Real.log_neg (pos_at_place _ _) (hu k.val i.val hne))
    exact_mod_cast mult_pos
  have hpos : ∀ (k : {w : NumberField.InfinitePlace F //
      w ≠ dirichletUnitTheorem.w₀}), 0 < ∑ i, (v k) i := by
    intro k
    rw [dirichletUnitTheorem.sum_logEmbedding_component (u k.val)]
    refine mul_pos_of_neg_of_neg ?_
      (Real.log_neg (pos_at_place _ _) (hu k.val _ (Ne.symm k.prop)))
    exact neg_lt_zero.mpr (by exact_mod_cast mult_pos)
  have hdet : B.det v ≠ 0 := by
    rw [Module.Basis.det_apply]
    refine det_ne_zero_of_sum_col_lt_diag (fun k ↦ ?_)
    simp_rw [Real.norm_eq_abs, B,
      Module.Basis.coePiBasisFun.toMatrix_eq_transpose, Matrix.transpose_apply]
    have e1 : ∑ i ∈ Finset.univ.erase k, |(v k) i| =
        -(∑ i ∈ Finset.univ.erase k, (v k) i) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun i hi => abs_of_neg (hneg k i hi))
    have hmem : k ∈ (Finset.univ : Finset _) := Finset.mem_univ k
    have hsplit := Finset.add_sum_erase Finset.univ (fun i => (v k) i) hmem
    have hsum : ∑ i ∈ Finset.univ.erase k, (v k) i ≤ 0 :=
      Finset.sum_nonpos (fun i hi => le_of_lt (hneg k i hi))
    have hdiag : 0 < (v k) k := by linarith [hpos k, hsplit]
    rw [e1, abs_of_pos hdiag]
    linarith [hpos k, hsplit]
  have hLI : LinearIndependent ℝ v :=
    ((Module.Basis.is_basis_iff_det B).mpr (isUnit_iff_ne_zero.mpr hdet)).1
  have hmax : IsMaxRank (fun i : Fin (rank F) => u ((equivFinRank F i).val)) :=
    (linearIndependent_equiv (equivFinRank F)).mpr hLI
  have hfin : (Subgroup.closure (Set.range (fun i : Fin (rank F) =>
      u ((equivFinRank F i).val)))).FiniteIndex :=
    isMaxRank_iff_closure_finiteIndex.mp hmax
  have hsub : Subgroup.closure (Set.range (fun i : Fin (rank F) =>
      u ((equivFinRank F i).val))) ≤ Subgroup.closure (Set.range u) := by
    apply Subgroup.closure_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨(equivFinRank F i).val, rfl⟩
  exact @Subgroup.finiteIndex_of_le _ _ _ _ hfin hsub

end NumberField.Units


-- created on 2026-10-20
-- updated on 2026-10-28
