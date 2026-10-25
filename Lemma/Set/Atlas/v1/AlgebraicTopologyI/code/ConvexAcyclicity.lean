import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.AlgebraicTopologyI.code.ConvexAcyclicity.Part2
open Finset BigOperators AlgebraicTopologyI


namespace AlgebraicTopologyI

/--
[singularSimplex_punit_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/ConvexAcyclicity.lean)
-/
@[path]
lemma singularSimplex_punit_unique
  {n : ℕ}
  {σ τ : SingularSimplex n PUnit} :
-- imply
  σ = τ :=
-- proof
  ContinuousMap.ext fun _ => Subsingleton.elim _ _

end AlgebraicTopologyI

namespace AlgebraicTopologyI

/--
[singularChains_punit_multiple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/ConvexAcyclicity.lean)
-/
@[path]
lemma singularChains_punit_multiple
  {n : ℕ}
  {σ₀ : SingularSimplex n PUnit}
  {c : SingularChains n PUnit} :
-- imply
  ∃ m : ℤ, c = m • FreeAbelianGroup.of σ₀ := by
-- proof
  induction c using FreeAbelianGroup.induction_on with
  | zero => exact ⟨0, by simp⟩
  | of a => exact ⟨1, by rw [one_smul, singularSimplex_punit_unique n a σ₀]⟩
  | neg a => exact ⟨-1, by simp [singularSimplex_punit_unique n a σ₀]⟩
  | add a b ha hb =>
    obtain ⟨m, rfl⟩ := ha; obtain ⟨k, rfl⟩ := hb
    exact ⟨m + k, by rw [add_smul]⟩

end AlgebraicTopologyI

namespace AlgebraicTopologyI

/--
[freeAbelianGroup_smul_of_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/ConvexAcyclicity.lean)
-/
@[path]
lemma freeAbelianGroup_smul_of_eq_zero
  {a : T}
  {m : ℤ}
-- given
  (h : m • FreeAbelianGroup.of a = (0 : FreeAbelianGroup T)) :
-- imply
  m = 0 := by
-- proof
  have : (FreeAbelianGroup.lift (fun _ => (1 : ℤ))) (m • FreeAbelianGroup.of a) = 0 := by
    rw [h, map_zero]
  rw [map_zsmul, FreeAbelianGroup.lift_apply_of] at this
  simpa using this

end AlgebraicTopologyI

namespace AlgebraicTopologyI

/--
[alternating_sum_range_parity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/ConvexAcyclicity.lean)
-/
@[path]
lemma alternating_sum_range_parity
  {N : ℕ} :
-- imply
  ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i = if Odd N then 1 else 0 := by
-- proof
  induction N with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]; simp only [Nat.odd_add_one]
    by_cases hk : Odd k
    · simp only [hk, not_true_eq_false, ite_true, ite_false]; rw [hk.neg_one_pow]; ring
    · simp only [hk, not_false_eq_true, ite_false, ite_true]
      rw [(Nat.not_odd_iff_even.mp hk).neg_one_pow]; ring

end AlgebraicTopologyI

namespace AlgebraicTopologyI

/--
[alternating_sum_fin_parity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/ConvexAcyclicity.lean)
-/
@[path]
lemma alternating_sum_fin_parity
  {n : ℕ} :
-- imply
  (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ)) = if Odd n then 1 else 0 := by
-- proof
  rw [Fin.sum_univ_eq_sum_range, alternating_sum_range_parity]
  simp only [show Odd (n + 2) ↔ Odd n from
    ⟨fun ⟨k, hk⟩ => ⟨k - 1, by omega⟩, fun ⟨k, hk⟩ => ⟨k + 1, by omega⟩⟩]

end AlgebraicTopologyI

namespace AlgebraicTopologyI

/--
[boundaryMap_punit_gen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/ConvexAcyclicity.lean)
-/
@[path]
lemma boundaryMap_punit_gen
  {n : ℕ}
  {σ : SingularSimplex (n + 1) PUnit}
  {σ₀ : SingularSimplex n PUnit} :
-- imply
  boundaryMap n PUnit (FreeAbelianGroup.of σ) = (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ)) • FreeAbelianGroup.of σ₀ := by
-- proof
  show (FreeAbelianGroup.lift (fun σ =>
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • FreeAbelianGroup.of (SingularSimplex.face i σ)))
    (FreeAbelianGroup.of σ) = _
  erw [FreeAbelianGroup.lift_apply_of]
  conv_rhs => rw [show (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ)) • FreeAbelianGroup.of σ₀ =
    ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • FreeAbelianGroup.of σ₀
    from by rw [← Finset.sum_smul]]
  simp_rw [singularSimplex_punit_unique n _ σ₀]

end AlgebraicTopologyI

/--
[stdSimplex_coord_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/ConvexAcyclicity.lean)
-/
@[path]
private lemma stdSimplex_coord_le_one_eq
  {m : ℕ}
  {x : ↥(stdSimplex ℝ (Fin m))}
  {i : Fin m} :
-- imply
  x.1 i ≤ 1 := by
-- proof
  apply AlgebraicTopologyI.stdSimplex_coord_le_one x i

/--
[coneSimplex_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/ConvexAcyclicity.lean)
-/
@[path]
private lemma coneSimplex_continuous_eq
  {m n : ℕ}
  {b : ↥(stdSimplex ℝ (Fin m))}
  {σ : C(↥(stdSimplex ℝ (Fin (n + 1))), ↥(stdSimplex ℝ (Fin m)))} :
-- imply
  Continuous (coneRawSimplex m n b σ) := by
-- proof
  apply AlgebraicTopologyI.coneSimplex_continuous m n b σ

/--
[coneSimplex_face_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/ConvexAcyclicity.lean)
-/
@[path]
private lemma coneSimplex_face_zero_eq
  {p q n : ℕ}
  {σ : SingularSimplex (n + 1) (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1))))} :
-- imply
  SingularSimplex.face 0 (coneSimplex p q (n + 1) σ) = σ := by
-- proof
  apply AlgebraicTopologyI.coneSimplex_face_zero p q n σ

/--
[insertNth_succ_zero'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/ConvexAcyclicity.lean)
-/
@[path]
private lemma insertNth_succ_zero'_eq
  {n : ℕ}
  {i : Fin (n + 2)}
  {f : Fin (n + 2) → ℝ} :
-- imply
  @Fin.insertNth (n + 2) (fun _ => ℝ) i.succ 0 f 0 = f 0 := by
-- proof
  apply AlgebraicTopologyI.insertNth_succ_zero' n i f

/--
[insertNth_succ_succ'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/ConvexAcyclicity.lean)
-/
@[path]
private lemma insertNth_succ_succ'_eq
  {n : ℕ}
  {i : Fin (n + 2)}
  {f : Fin (n + 2) → ℝ}
  {j : Fin (n + 2)} :
-- imply
  @Fin.insertNth (n + 2) (fun _ => ℝ) i.succ 0 f (Fin.succ j) = @Fin.insertNth (n + 1) (fun _ => ℝ) i 0 (fun k : Fin (n + 1) => f (Fin.succ k)) j := by
-- proof
  apply AlgebraicTopologyI.insertNth_succ_succ' n i f j

/--
[rescaleTail_faceInclusion_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/ConvexAcyclicity.lean)
-/
@[path]
private lemma rescaleTail_faceInclusion_succ_eq
  {n : ℕ}
  {i : Fin (n + 2)}
  {t : ↥(stdSimplex ℝ (Fin (n + 2)))}
-- given
  (ht : t.1 0 ≠ 1) :
-- imply
  rescaleTail (n + 1) ⟨Fin.insertNth i.succ 0 t.1, faceMap_mem_stdSimplex (n + 1) i.succ t.1 t.2⟩ = ⟨Fin.insertNth i 0 (rescaleTail n t).1, faceMap_mem_stdSimplex n i (rescaleTail n t).1 (rescaleTail n t).2⟩ := by
-- proof
  apply AlgebraicTopologyI.rescaleTail_faceInclusion_succ n i t ht

/--
[coneSimplex_face_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/ConvexAcyclicity.lean)
-/
@[path]
private lemma coneSimplex_face_succ_eq
  {p q n : ℕ}
  {i : Fin (n + 2)}
  {σ : SingularSimplex (n + 1) (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1))))} :
-- imply
  SingularSimplex.face i.succ (coneSimplex p q (n + 1) σ) = coneSimplex p q n (SingularSimplex.face i σ) := by
-- proof
  apply AlgebraicTopologyI.coneSimplex_face_succ p q n i σ

/--
[coneSimplex_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/ConvexAcyclicity.lean)
-/
@[path]
private lemma coneSimplex_boundary_eq
  {p q n : ℕ}
  {c : SingularChains (n + 1) (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1))))} :
-- imply
  boundaryMap (n + 1) (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1)))) (coneChain p q (n + 1) c) = c - coneChain p q n (boundaryMap n (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1)))) c) := by
-- proof
  apply AlgebraicTopologyI.coneSimplex_boundary p q n c

/--
[stdSimplex_prod_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/ConvexAcyclicity.lean)
-/
@[path]
private lemma stdSimplex_prod_acyclic_eq
  {p q n : ℕ}
  {c : SingularChains (n + 1) (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1))))}
-- given
  (hc : boundaryMap n (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1)))) c = 0) :
-- imply
  ∃ d : SingularChains (n + 2) (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1)))), boundaryMap (n + 1) (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1)))) d = c := by
-- proof
  apply AlgebraicTopologyI.stdSimplex_prod_acyclic p q n c hc


-- created on 2026-10-23
