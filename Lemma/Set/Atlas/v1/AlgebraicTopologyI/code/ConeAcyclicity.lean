import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.AlgebraicTopologyI.code.ConeAcyclicity
open Finset BigOperators AlgebraicTopologyI


namespace AlgebraicTopologyI

/--
[SingularChains.map_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/ConeAcyclicity.lean)
-/
@[path]
lemma SingularChains.map_id
  {n : ℕ}
  {X : Type}
  [TopologicalSpace X]
  {c : SingularChains n X} :
-- imply
  SingularChains.map (ContinuousMap.id X) c = c := by
-- proof
  show FreeAbelianGroup.map (SingularSimplex.map (ContinuousMap.id X)) c = c
  suffices h : (SingularSimplex.map (ContinuousMap.id X) :
    SingularSimplex n X → SingularSimplex n X) = _root_.id by
    rw [h, FreeAbelianGroup.map_id]; rfl
  funext σ; exact ContinuousMap.id_comp σ

end AlgebraicTopologyI

namespace AlgebraicTopologyI

/--
[singularSimplex_punit_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/ConeAcyclicity.lean)
-/
@[path]
lemma singularSimplex_punit_eq
  {n : ℕ}
  {σ τ : SingularSimplex n PUnit} :
-- imply
  σ = τ :=
-- proof
  ContinuousMap.ext fun _ => Subsingleton.elim _ _

end AlgebraicTopologyI

namespace AlgebraicTopologyI

/--
[singularChains_punit_eq_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/ConeAcyclicity.lean)
-/
@[path]
lemma singularChains_punit_eq_smul
  {n : ℕ}
  {σ₀ : SingularSimplex n PUnit}
  {c : SingularChains n PUnit} :
-- imply
  ∃ m : ℤ, c = m • FreeAbelianGroup.of σ₀ := by
-- proof
  induction c using FreeAbelianGroup.induction_on with
  | zero => exact ⟨0, by simp⟩
  | of a =>
    exact ⟨1, by rw [one_smul, singularSimplex_punit_eq n a σ₀]⟩
  | neg a =>
    exact ⟨-1, by simp [singularSimplex_punit_eq n a σ₀]⟩
  | add a b ha hb =>
    obtain ⟨m, rfl⟩ := ha; obtain ⟨k, rfl⟩ := hb
    exact ⟨m + k, by rw [add_smul]⟩

end AlgebraicTopologyI

namespace AlgebraicTopologyI

/--
[FreeAbelianGroup.smul_of_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/ConeAcyclicity.lean)
-/
@[path]
lemma FreeAbelianGroup.smul_of_eq_zero
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
[alternating_sum_range](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/ConeAcyclicity.lean)
-/
@[path]
lemma alternating_sum_range
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
[alternating_sum_fin](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/ConeAcyclicity.lean)
-/
@[path]
lemma alternating_sum_fin
  {n : ℕ} :
-- imply
  (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ)) = if Odd n then 1 else 0 := by
-- proof
  rw [Fin.sum_univ_eq_sum_range, alternating_sum_range]
  simp only [show Odd (n + 2) ↔ Odd n from
    ⟨fun ⟨k, hk⟩ => ⟨k - 1, by omega⟩, fun ⟨k, hk⟩ => ⟨k + 1, by omega⟩⟩]

end AlgebraicTopologyI

namespace AlgebraicTopologyI

/--
[boundaryMap_punit_generator](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/ConeAcyclicity.lean)
-/
@[path]
lemma boundaryMap_punit_generator
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
  simp_rw [singularSimplex_punit_eq n _ σ₀]

end AlgebraicTopologyI

namespace AlgebraicTopologyI

/--
[punit_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/ConeAcyclicity.lean)
-/
@[path]
lemma punit_acyclic
  {n : ℕ}
  {c : SingularChains (n + 1) PUnit}
-- given
  (hc : boundaryMap n PUnit c = 0) :
-- imply
  ∃ d : SingularChains (n + 2) PUnit, boundaryMap (n + 1) PUnit d = c := by
-- proof
  let σ₁ : SingularSimplex (n + 1) PUnit := ContinuousMap.const _ PUnit.unit
  let σ₀ : SingularSimplex n PUnit := ContinuousMap.const _ PUnit.unit
  let σ₂ : SingularSimplex (n + 2) PUnit := ContinuousMap.const _ PUnit.unit
  obtain ⟨m, rfl⟩ := singularChains_punit_eq_smul (n + 1) σ₁ c
  have hbd := boundaryMap_punit_generator n σ₁ σ₀
  have hc2 : m * (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ)) = 0 := by
    have h1 : (boundaryMap n PUnit) (m • FreeAbelianGroup.of σ₁) =
      m • (boundaryMap n PUnit) (FreeAbelianGroup.of σ₁) := map_zsmul _ m _
    rw [h1, hbd] at hc
    have h2 : (m * (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ))) • FreeAbelianGroup.of σ₀ = 0 := by
      rw [mul_comm, mul_smul]
      have := (smul_comm (m : ℤ)
        (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ)) (FreeAbelianGroup.of σ₀)).symm
      exact this ▸ hc
    exact FreeAbelianGroup.smul_of_eq_zero σ₀ _ h2
  rw [alternating_sum_fin] at hc2
  by_cases hn : Odd n
  · simp only [hn, ite_true, mul_one] at hc2
    rw [hc2, zero_smul]
    exact ⟨0, map_zero _⟩
  · have hbd2 := boundaryMap_punit_generator (n + 1) σ₂ σ₁
    refine ⟨m • FreeAbelianGroup.of σ₂, ?_⟩
    have h2 : (boundaryMap (n + 1) PUnit) (m • FreeAbelianGroup.of σ₂) =
      m • (boundaryMap (n + 1) PUnit) (FreeAbelianGroup.of σ₂) := map_zsmul _ m _
    rw [h2, hbd2]
    have hodd : Odd (n + 1) := Nat.odd_add_one.mpr hn
    simp only [alternating_sum_fin, hodd, ite_true, one_smul]
    rfl
end



-- created on 2026-10-23
