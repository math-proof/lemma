import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.SobolevHilbert
open MeasureTheory SobolevHilbert


namespace SobolevHilbert

/--
[japaneseBracket_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevHilbert.lean)
-/
@[path]
lemma japaneseBracket_pos
  [NormedAddCommGroup E]
  {ξ : E} :
-- imply
  0 < japaneseBracket ξ := by
-- proof
  simp only [japaneseBracket]
  apply Real.sqrt_pos_of_pos
  positivity

end SobolevHilbert

namespace SobolevHilbert

/--
[sobolevWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevHilbert.lean)
-/
@[path]
lemma sobolevWeight_pos
  [NormedAddCommGroup E]
  {m : ℝ}
  {ξ : E} :
-- imply
  0 < sobolevWeight m ξ := by
-- proof
  simp only [sobolevWeight]
  positivity

end SobolevHilbert

namespace SobolevHilbert

/--
[proposition_9_8](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevHilbert.lean)
-/
@[path]
lemma proposition_9_8
  {n : ℕ}
  {m : ℝ} :
-- imply
  (∃ Φ : SobolevSpace.Hs n m ≃ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))), DenseRange (Φ.symm ∘ (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))))) ∧ Nonempty (SobolevSpace.Hs n (-m) ≃ₗᵢ⋆[ℂ] (SobolevSpace.Hs n m →L[ℂ] ℂ)) :=
-- proof
  SobolevSpace.proposition_9_8 n m
end SobolevHilbert


/--
[sobolevSpace_contDiff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevHilbert.lean)
-/
@[path]
private lemma sobolevSpace_contDiff_eq
  {n m : ℕ}
  {u : SobolevEmbedding.SobolevSpace n m}
  {j : ℕ}
-- given
  (hj : j ≤ m) :
-- imply
  ContDiff ℝ (j : ℕ∞) u.toFun := by
-- proof
  apply SobolevHilbert.sobolevSpace_contDiff u j hj

/--
[sobolevSpace_add_memLp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevHilbert.lean)
-/
@[path]
private lemma sobolevSpace_add_memLp_eq
  {n m : ℕ}
  {u v : SobolevEmbedding.SobolevSpace n m}
  {j : ℕ}
-- given
  (hj : j ≤ m) :
-- imply
  MemLp (fun x => iteratedFDeriv ℝ j (u.toFun + v.toFun) x) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
-- proof
  apply SobolevHilbert.sobolevSpace_add_memLp u v j hj

/--
[l2_triangle_range](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevHilbert.lean)
-/
@[path]
private lemma l2_triangle_range_eq
  {k : ℕ}
  {a b : ℕ → ℝ} :
-- imply
  Real.sqrt (∑ j ∈ Finset.range k, (a j + b j) ^ 2) ≤ Real.sqrt (∑ j ∈ Finset.range k, (a j) ^ 2) + Real.sqrt (∑ j ∈ Finset.range k, (b j) ^ 2) := by
-- proof
  apply SobolevHilbert.l2_triangle_range k a b

/--
[sqrt_sum_sq_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevHilbert.lean)
-/
@[path]
private lemma sqrt_sum_sq_mono_eq
  {k : ℕ}
  {c d : ℕ → ℝ}
-- given
  (hc : ∀ j ∈ Finset.range k, 0 ≤ c j)
  (hle : ∀ j ∈ Finset.range k, c j ≤ d j) :
-- imply
  Real.sqrt (∑ j ∈ Finset.range k, (c j) ^ 2) ≤ Real.sqrt (∑ j ∈ Finset.range k, (d j) ^ 2) := by
-- proof
  apply SobolevHilbert.sqrt_sum_sq_mono hc hle

/--
[sobolevSpace_norm_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevHilbert.lean)
-/
@[path]
private lemma sobolevSpace_norm_triangle_eq
  {n m : ℕ}
  {u v : SobolevEmbedding.SobolevSpace n m} :
-- imply
  Real.sqrt (∑ j ∈ Finset.range (m + 1), (eLpNorm (fun x => iteratedFDeriv ℝ j (u.toFun + v.toFun) x) 2 volume).toReal ^ 2) ≤ Real.sqrt (∑ j ∈ Finset.range (m + 1), (eLpNorm (fun x => iteratedFDeriv ℝ j u.toFun x) 2 volume).toReal ^ 2) + Real.sqrt (∑ j ∈ Finset.range (m + 1), (eLpNorm (fun x => iteratedFDeriv ℝ j v.toFun x) 2 volume).toReal ^ 2) := by
-- proof
  apply SobolevHilbert.sobolevSpace_norm_triangle u v

/--
[sobolevSpace_ae_eq_zero_imp_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevHilbert.lean)
-/
@[path]
private lemma sobolevSpace_ae_eq_zero_imp_eq_zero_eq
  {n m : ℕ}
  {u : SobolevEmbedding.SobolevSpace n m}
-- given
  (hae : u.toFun =ᵐ[volume] 0) :
-- imply
  u.toFun = 0 := by
-- proof
  apply SobolevHilbert.sobolevSpace_ae_eq_zero_imp_eq_zero u hae

/--
[sobolevSpace_norm_separation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevHilbert.lean)
-/
@[path]
private lemma sobolevSpace_norm_separation_eq
  {n m : ℕ}
  {u : SobolevEmbedding.SobolevSpace n m}
-- given
  (h : ∀ j, j ≤ m → (eLpNorm (fun x => iteratedFDeriv ℝ j u.toFun x) 2 volume).toReal = 0) :
-- imply
  u.toFun = 0 := by
-- proof
  apply SobolevHilbert.sobolevSpace_norm_separation u h

/--
[SobolevEmbedding.SobolevSpace.ext'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevHilbert.lean)
-/
@[path]
private lemma ext'_eq
  {n m : ℕ}
  {u v : SobolevEmbedding.SobolevSpace n m}
-- given
  (h : u.toFun = v.toFun) :
-- imply
  u = v := by
-- proof
  apply SobolevHilbert.SobolevEmbedding.SobolevSpace.ext' h

/--
[sobolevSpace_add_toFun](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevHilbert.lean)
-/
@[path]
private lemma sobolevSpace_add_toFun_eq
  {n m : ℕ}
  {u v : SobolevEmbedding.SobolevSpace n m} :
-- imply
  (u + v).toFun = u.toFun + v.toFun := by
-- proof
  apply SobolevHilbert.sobolevSpace_add_toFun u v

/--
[sobolevSpace_neg_toFun](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevHilbert.lean)
-/
@[path]
private lemma sobolevSpace_neg_toFun_eq
  {n m : ℕ}
  {u : SobolevEmbedding.SobolevSpace n m} :
-- imply
  (-u).toFun = -u.toFun := by
-- proof
  apply SobolevHilbert.sobolevSpace_neg_toFun u

/--
[sobolevSpace_zero_toFun](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevHilbert.lean)
-/
@[path]
private lemma sobolevSpace_zero_toFun_eq
  {n m : ℕ} :
-- imply
  (0 : SobolevEmbedding.SobolevSpace n m).toFun = 0 := by
-- proof
  apply SobolevHilbert.sobolevSpace_zero_toFun n m

/--
[sobolevNorm_neg'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevHilbert.lean)
-/
@[path]
private lemma sobolevNorm_neg'_eq
  {n m : ℕ}
  {u : SobolevEmbedding.SobolevSpace n m} :
-- imply
  sobolevNorm (-u) = sobolevNorm u := by
-- proof
  apply SobolevHilbert.sobolevNorm_neg' u

/--
[sobolevNorm_zero'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevHilbert.lean)
-/
@[path]
private lemma sobolevNorm_zero'_eq
  {n m : ℕ} :
-- imply
  sobolevNorm (0 : SobolevEmbedding.SobolevSpace n m) = 0 := by
-- proof
  apply SobolevHilbert.sobolevNorm_zero' n m

/--
[sobolevNorm_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevHilbert.lean)
-/
@[path]
private lemma sobolevNorm_eq_zero_iff_eq
  {n m : ℕ}
  {u : SobolevEmbedding.SobolevSpace n m}
-- given
  (h : sobolevNorm u = 0) :
-- imply
  u = 0 := by
-- proof
  apply SobolevHilbert.sobolevNorm_eq_zero_iff u h

/--
[sobolevSpace_smul_memLp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevHilbert.lean)
-/
@[path]
private lemma sobolevSpace_smul_memLp_eq
  {n m : ℕ}
  {c : ℂ}
  {u : SobolevEmbedding.SobolevSpace n m}
  {j : ℕ}
-- given
  (hj : j ≤ m) :
-- imply
  MemLp (fun x => iteratedFDeriv ℝ j (c • u.toFun) x) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
-- proof
  apply SobolevHilbert.sobolevSpace_smul_memLp c u j hj

/--
[sobolevSpace_smul_toFun](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevHilbert.lean)
-/
@[path]
private lemma sobolevSpace_smul_toFun_eq
  {n m : ℕ}
  {c : ℂ}
  {u : SobolevEmbedding.SobolevSpace n m} :
-- imply
  (c • u).toFun = c • u.toFun := by
-- proof
  apply SobolevHilbert.sobolevSpace_smul_toFun c u

/--
[sobolevSpace_norm_smul_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevHilbert.lean)
-/
@[path]
private lemma sobolevSpace_norm_smul_le_eq
  {n m : ℕ}
  {c : ℂ}
  {u : SobolevEmbedding.SobolevSpace n m} :
-- imply
  @Norm.norm _ (sobolevSpace_nacg n m).toNorm (c • u) ≤ ‖c‖ * @Norm.norm _ (sobolevSpace_nacg n m).toNorm u := by
-- proof
  apply SobolevHilbert.sobolevSpace_norm_smul_le c u

/--
[schwartz_iteratedFDeriv_memLp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevHilbert.lean)
-/
@[path]
private lemma schwartz_iteratedFDeriv_memLp_eq
  {n m : ℕ}
  {φ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ}
  {j : ℕ}
-- given
  (hj : j ≤ m) :
-- imply
  MemLp (fun x => iteratedFDeriv ℝ j (⇑φ) x) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
-- proof
  apply SobolevHilbert.schwartz_iteratedFDeriv_memLp φ j hj

/--
[schwartzToSobolev_toFun](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevHilbert.lean)
-/
@[path]
private lemma schwartzToSobolev_toFun_eq
  {n m : ℕ}
  {φ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ} :
-- imply
  (schwartzToSobolev n m φ).toFun = ⇑φ := by
-- proof
  apply SobolevHilbert.schwartzToSobolev_toFun n m φ


-- created on 2026-10-23
