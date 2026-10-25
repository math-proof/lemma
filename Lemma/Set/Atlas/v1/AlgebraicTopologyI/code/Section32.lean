import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicTopologyI.code.Section32.Part2
open Set Function OrientationTheorem


namespace OrientationTheorem

/--
[orientation_theorem_union_of_ladder](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section32.lean)
-/
@[path]
lemma orientation_theorem_union_of_ladder
  [TopologicalSpace M]
  {n : ℕ}
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {A B : Set M}
  {Hrel : ℕ → Set M → Type*}
  [∀ q K, AddCommGroup (Hrel q K)]
  {Γsec : Set M → Type*}
  [∀ K, AddCommGroup (Γsec K)]
  {jMap : (K : Set M) → Hrel n K →+ Γsec K}
  {ladder : MayerVietorisLadder n Hrel Γsec jMap A B}
-- given
  (_hA : IsClosed A)
  (_hB : IsClosed B)
  (hOT_A : OrientationTheoremResult n Hrel Γsec jMap A)
  (hOT_B : OrientationTheoremResult n Hrel Γsec jMap B)
  (hOT_AB : OrientationTheoremResult n Hrel Γsec jMap (A ∩ B)) :
-- imply
  OrientationTheoremResult n Hrel Γsec jMap (A ∪ B) := by
-- proof
  constructor
  ·
    intro q hq x
    obtain ⟨αq, h_inj_q⟩ := ladder.mv_inj_q q hq
    have h_prod_zero : ∀ y : Hrel q A × Hrel q B, y = 0 :=
      fun ⟨a, b⟩ => Prod.ext (hOT_A.vanishing q hq a) (hOT_B.vanishing q hq b)
    have hα : αq x = 0 := h_prod_zero (αq x)
    exact h_inj_q x hα
  ·
    have j_prod_bij : Bijective (AddMonoidHom.prodMap (jMap A) (jMap B)) :=
      hOT_A.isomorphism.prodMap hOT_B.isomorphism
    have h_top_ex₁ : Exact (0 : PUnit.{1} →+ PUnit.{1})
      (0 : PUnit.{1} →+ Hrel n (A ∪ B)) := by
      intro ⟨⟩; simp [Set.mem_range]
    have h_top_ex₂ : Exact (0 : PUnit.{1} →+ Hrel n (A ∪ B)) ladder.mvα := by
      intro y; constructor
      · exact fun h => ⟨⟨⟩, (ladder.mv_inj y h).symm⟩
      · rintro ⟨⟨⟩, rfl⟩; simp
    have h_bot_ex₁ : Exact (0 : PUnit.{1} →+ PUnit.{1})
      (0 : PUnit.{1} →+ Γsec (A ∪ B)) := by
      intro ⟨⟩; simp [Set.mem_range]
    have h_bot_ex₂ : Exact (0 : PUnit.{1} →+ Γsec (A ∪ B)) ladder.secα := by
      intro y; constructor
      · exact fun h => ⟨⟨⟩, (ladder.sec_inj y h).symm⟩
      · rintro ⟨⟨⟩, rfl⟩; simp
    have h_comm_zero : (0 : PUnit.{1} →+ Γsec (A ∪ B)).comp
      (0 : PUnit.{1} →+ PUnit.{1}) =
      (jMap (A ∪ B)).comp (0 : PUnit.{1} →+ Hrel n (A ∪ B)) := by
      ext ⟨⟩; simp
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
      (0 : PUnit.{1} →+ PUnit.{1}) (0 : PUnit.{1} →+ Hrel n (A ∪ B))
      ladder.mvα ladder.mvβ
      (0 : PUnit.{1} →+ PUnit.{1}) (0 : PUnit.{1} →+ Γsec (A ∪ B))
      ladder.secα ladder.secβ
      (0 : PUnit.{1} →+ PUnit.{1}) (0 : PUnit.{1} →+ PUnit.{1})
      (jMap (A ∪ B)) (AddMonoidHom.prodMap (jMap A) (jMap B)) (jMap (A ∩ B))
      rfl h_comm_zero ladder.comm_α ladder.comm_β
      h_top_ex₁ h_top_ex₂ ladder.mv_exact
      h_bot_ex₁ h_bot_ex₂ ladder.sec_exact
      (fun ⟨⟩ => ⟨⟨⟩, rfl⟩)
      ⟨fun _ _ _ => Subsingleton.elim _ _, fun ⟨⟩ => ⟨⟨⟩, rfl⟩⟩
      j_prod_bij
      hOT_AB.isomorphism.injective

end OrientationTheorem

namespace OrientationTheorem

/--
[compact_decreasing_sequence_subset_open](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section32.lean)
-/
@[path]
lemma compact_decreasing_sequence_subset_open
  [TopologicalSpace M]
  [TopologicalSpace X]
  [T2Space X]
  {A : ℕ → Set X}
  {U : Set X}
-- given
  (hA_compact : ∀ i, IsCompact (A i))
  (hA_decreasing : ∀ i, A (i + 1) ⊆ A i)
  (hU_open : IsOpen U)
  (hAU : ⋂ i, A i ⊆ U) :
-- imply
  ∃ i, A i ⊆ U := by
-- proof
  by_contra h
  push Not at h
  have hne : ∀ i, (A i \ U).Nonempty :=
    fun i => Set.nonempty_of_not_subset (h i)
  have hdecr : ∀ i, A (i + 1) \ U ⊆ A i \ U :=
    fun i => diff_subset_diff_left (hA_decreasing i)
  have hclosed : ∀ i, IsClosed (A i \ U) :=
    fun i => (hA_compact i).isClosed.sdiff hU_open
  have hcompact0 : IsCompact (A 0 \ U) := (hA_compact 0).diff hU_open
  have hinter := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun i => A i \ U) hdecr hne hcompact0 hclosed
  have heq : ⋂ i, A i \ U = (⋂ i, A i) \ U := by
    simp only [diff_eq]
    exact (iInter_inter Uᶜ A).symm
  rw [heq, Set.diff_eq_empty.mpr hAU] at hinter
  exact Set.not_nonempty_empty hinter
variable {n : ℕ}
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {Hrel : ℕ → Set M → Type*}
  [∀ q K, AddCommGroup (Hrel q K)]
  {Γsec : Set M → Type*}
  [∀ K, AddCommGroup (Γsec K)]
  {jMap : (K : Set M) → Hrel n K →+ Γsec K}

end OrientationTheorem

namespace OrientationTheorem

/--
[result_finset_biUnion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section32.lean)
-/
@[path]
lemma result_finset_biUnion
  [TopologicalSpace M]
  {n : ℕ}
  [DecidableEq ι]
-- given
  (union_step : ∀ (K₁ K₂ : Set M), IsClosed K₁ → IsClosed K₂ → OrientationTheoremResult n Hrel Γsec jMap K₁ → OrientationTheoremResult n Hrel Γsec jMap K₂ → OrientationTheoremResult n Hrel Γsec jMap (K₁ ∩ K₂) → OrientationTheoremResult n Hrel Γsec jMap (K₁ ∪ K₂)) :
-- imply
  ∀ (k : ℕ) (D : ι → Set M) (_ : ∀ i, IsClosed (D i)) (_ : ∀ (S : Finset ι), S.Nonempty → OrientationTheoremResult n Hrel Γsec jMap (⋂ i ∈ S, D i)) (T : Finset ι) (_ : T.Nonempty) (_ : T.card ≤ k), OrientationTheoremResult n Hrel Γsec jMap (⋃ i ∈ T, D i) := by
-- proof
  intro k
  induction k with
  | zero =>
    intro D _ _ T hT hk
    have := hT.card_pos; omega
  | succ k ih =>
    intro D hD_closed hbase T hT hk
    obtain ⟨j, hj⟩ := hT
    by_cases hT' : (T.erase j).Nonempty
    · have hcard_erase : (T.erase j).card ≤ k := by
      have := Finset.card_erase_of_mem hj; omega
      have hT_eq : (⋃ i ∈ T, D i) = D j ∪ (⋃ i ∈ T.erase j, D i) := by
        rw [show T = insert j (T.erase j) from (Finset.insert_erase hj).symm]; simp
      rw [hT_eq]
      apply union_step
      · exact hD_closed j
      · exact isClosed_biUnion_finset (fun i _ => hD_closed i)
      · have : D j = ⋂ i ∈ ({j} : Finset ι), D i := by simp
        rw [this]; exact hbase {j} (Finset.singleton_nonempty j)
      · exact ih D hD_closed hbase (T.erase j) hT' hcard_erase
      · rw [inter_iUnion₂]
        apply ih (fun i => D j ∩ D i)
          (fun i => (hD_closed j).inter (hD_closed i))
          (fun S hS => by
            have : (⋂ i ∈ S, (D j ∩ D i)) = ⋂ i ∈ insert j S, D i := by
              ext x; simp only [mem_iInter, Finset.mem_insert, mem_inter_iff]
              constructor
              · intro h i hi
                obtain rfl | hi := hi
                · obtain ⟨s, hs⟩ := hS; exact (h s hs).1
                · exact (h i hi).2
              · intro h i hi; exact ⟨h j (Or.inl rfl), h i (Or.inr hi)⟩
            rw [this]
            exact hbase (insert j S) (Finset.insert_nonempty j S))
          (T.erase j) hT' hcard_erase
    · rw [Finset.not_nonempty_iff_eq_empty] at hT'
      have hT_single : T = {j} := by
        rw [← Finset.insert_erase hj, hT']; simp
      rw [hT_single]; simp
      have : D j = ⋂ i ∈ ({j} : Finset ι), D i := by simp
      rw [this]; exact hbase {j} (Finset.singleton_nonempty j)

end OrientationTheorem

namespace OrientationTheorem

/--
[orientation_theorem_from_cover](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section32.lean)
-/
@[path]
lemma orientation_theorem_from_cover
  [TopologicalSpace M]
  {n : ℕ}
  {n : ℕ}
  {A : Set M}
  [AlgebraicTopologyI.TopologicalManifold n M]
  {Hrel : ℕ → Set M → Type*}
  [∀ q K, AddCommGroup (Hrel q K)]
  {Γsec : Set M → Type*}
  [∀ K, AddCommGroup (Γsec K)]
  {jMap : (K : Set M) → Hrel n K →+ Γsec K}
  {m : ℕ}
  {D : Fin m → Set M}
-- given
  (_hA_compact : IsCompact A)
  (hA_closed : IsClosed A)
  (hD_closed : ∀ i, IsClosed (D i))
  (hD_cover : A ⊆ ⋃ i, D i)
  (hD_result : ∀ (S : Finset (Fin m)), S.Nonempty → OrientationTheoremResult n Hrel Γsec jMap (A ∩ ⋂ i ∈ S, D i))
  (union_step : ∀ (K₁ K₂ : Set M), IsClosed K₁ → IsClosed K₂ → OrientationTheoremResult n Hrel Γsec jMap K₁ → OrientationTheoremResult n Hrel Γsec jMap K₂ → OrientationTheoremResult n Hrel Γsec jMap (K₁ ∩ K₂) → OrientationTheoremResult n Hrel Γsec jMap (K₁ ∪ K₂))
  (hm_pos : 0 < m) :
-- imply
  OrientationTheoremResult n Hrel Γsec jMap A := by
-- proof
  have hA_eq : A = ⋃ i ∈ (Finset.univ : Finset (Fin m)), (A ∩ D i) := by
    ext x; simp only [Finset.mem_univ, iUnion_true, mem_iUnion, mem_inter_iff]
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hD_cover hx)
      exact ⟨i, hx, hi⟩
    · rintro ⟨i, hx, _⟩; exact hx
  rw [hA_eq]
  exact result_finset_biUnion union_step m (fun i => A ∩ D i)
    (fun i => hA_closed.inter (hD_closed i))
    (fun S hS => by
      have : (⋂ i ∈ S, (A ∩ D i)) = A ∩ ⋂ i ∈ S, D i := by
        ext x; simp only [mem_iInter, mem_inter_iff]
        constructor
        · intro h; exact ⟨(h _ hS.choose_spec).1, fun i hi => (h i hi).2⟩
        · rintro ⟨ha, hD⟩ i hi; exact ⟨ha, hD i hi⟩
      rw [this]; exact hD_result S hS)
    Finset.univ ⟨⟨0, hm_pos⟩, Finset.mem_univ _⟩ (Finset.card_fin m).le
end OrientationTheorem
namespace OrientationTheorem

end OrientationTheorem

namespace OrientationTheorem

/--
[RelativeHomologyColimitData.vanishing_propagation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section32.lean)
-/
@[path]
lemma RelativeHomologyColimitData.vanishing_propagation
  [TopologicalSpace M]
  [TopologicalSpace X]
  {A : ℕ → Set X}
  {G : Set X → Type*}
  [∀ K, AddCommGroup (G K)]
  {col : RelativeHomologyColimitData A G}
-- given
  (hvan : ∀ i, ∀ x : G (A i), x = 0) :
-- imply
  ∀ x : G (⋂ j, A j), x = 0 := by
-- proof
  intro x
  obtain ⟨i, g, hg⟩ := col.surj x
  rwa [hvan i g, map_zero] at hg

end OrientationTheorem

namespace OrientationTheorem

/--
[RelativeHomologyColimitData.bijective_propagation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section32.lean)
-/
@[path]
lemma RelativeHomologyColimitData.bijective_propagation
  [TopologicalSpace M]
  [TopologicalSpace X]
  {A : ℕ → Set X}
  {G H : Set X → Type*}
  [∀ K, AddCommGroup (G K)]
  [∀ K, AddCommGroup (H K)]
  {colG : RelativeHomologyColimitData A G}
  {colH : RelativeHomologyColimitData A H}
-- given
  (f : ∀ K, G K →+ H K)
  (hf_ρ : ∀ i, (colH.ρ i).comp (f (A i)) = (f (⋂ j, A j)).comp (colG.ρ i))
  (hf_φ : ∀ i j (hij : i ≤ j), (colH.φ i j hij).comp (f (A i)) = (f (A j)).comp (colG.φ i j hij))
  (hf_bij : ∀ i, Bijective (f (A i))) :
-- imply
  Bijective (f (⋂ j, A j)) := by
-- proof
  constructor
  ·
    intro a b hab
    suffices key : ∀ x : G (⋂ j, A j), f (⋂ j, A j) x = 0 → x = 0 by
      have hd := key (a - b) (by rw [map_sub, hab, sub_self])
      rwa [sub_eq_zero] at hd
    intro x hx
    obtain ⟨i, gi, hgi⟩ := colG.surj x
    have hc := DFunLike.congr_fun (hf_ρ i) gi
    simp only [AddMonoidHom.comp_apply] at hc
    rw [hgi, hx] at hc
    obtain ⟨j, hij, hφ⟩ := colH.inj i _ hc
    have hj := DFunLike.congr_fun (hf_φ i j hij) gi
    simp only [AddMonoidHom.comp_apply] at hj
    rw [hφ] at hj
    have hφG0 : colG.φ i j hij gi = 0 :=
      (hf_bij j).injective (hj.symm.trans (map_zero _).symm)
    have hρ := DFunLike.congr_fun (colG.compat i j hij) gi
    simp only [AddMonoidHom.comp_apply] at hρ
    rw [hφG0, map_zero] at hρ
    rw [← hgi, hρ]
  ·
    intro s
    obtain ⟨i, si, hsi⟩ := colH.surj s
    obtain ⟨gi, hgi⟩ := (hf_bij i).surjective si
    refine ⟨colG.ρ i gi, ?_⟩
    have := DFunLike.congr_fun (hf_ρ i) gi
    simp only [AddMonoidHom.comp_apply] at this
    rw [← this, hgi, hsi]

end OrientationTheorem

namespace OrientationTheorem

/--
[orientation_theorem_iInter](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section32.lean)
-/
@[path]
lemma orientation_theorem_iInter
  [TopologicalSpace M]
  [T2Space M]
  {n : ℕ}
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {A : ℕ → Set M}
  {Hrel : ℕ → Set M → Type*}
  [∀ q K, AddCommGroup (Hrel q K)]
  {Γsec : Set M → Type*}
  [∀ K, AddCommGroup (Γsec K)]
  {jMap : (K : Set M) → Hrel n K →+ Γsec K}
  {colΓ : RelativeHomologyColimitData A Γsec}
-- given
  (_hA_compact : ∀ i, IsCompact (A i))
  (_hA_decreasing : ∀ i, A (i + 1) ⊆ A i)
  (colH : ∀ q, RelativeHomologyColimitData A (Hrel q))
  (hjMap_ρ : ∀ i, (colΓ.ρ i).comp (jMap (A i)) = (jMap (⋂ j, A j)).comp ((colH n).ρ i))
  (hjMap_φ : ∀ i j (hij : i ≤ j), (colΓ.φ i j hij).comp (jMap (A i)) = (jMap (A j)).comp ((colH n).φ i j hij))
  (hsat : ∀ i, OrientationTheoremResult n Hrel Γsec jMap (A i)) :
-- imply
  OrientationTheoremResult n Hrel Γsec jMap (⋂ i, A i) where vanishing q hq x :=
-- proof
  (colH q).vanishing_propagation (fun i g => (hsat i).vanishing q hq g) x
  isomorphism :=
    RelativeHomologyColimitData.bijective_propagation (colH n) colΓ
      (fun K => jMap K) hjMap_ρ hjMap_φ (fun i => (hsat i).isomorphism)

end OrientationTheorem

namespace OrientationTheorem

/--
[orientation_theorem_iInter_manifold](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section32.lean)
-/
@[path]
lemma orientation_theorem_iInter_manifold
  [TopologicalSpace M]
  [TopologicalSpace M]
  {n : ℕ}
  [AlgebraicTopologyI.TopologicalManifold n M]
  {A : ℕ → Set M}
  {Hrel : ℕ → Set M → Type*}
  [∀ q K, AddCommGroup (Hrel q K)]
  {Γsec : Set M → Type*}
  [∀ K, AddCommGroup (Γsec K)]
  {jMap : (K : Set M) → Hrel n K →+ Γsec K}
  {cd : ColimitDataForDecreasingCompact n A Hrel Γsec jMap}
-- given
  (hA_compact : ∀ i, IsCompact (A i))
  (hA_decreasing : ∀ i, A (i + 1) ⊆ A i)
  (hsat : ∀ i, OrientationTheoremResult n Hrel Γsec jMap (A i)) :
-- imply
  OrientationTheoremResult n Hrel Γsec jMap (⋂ i, A i) :=
-- proof
  orientation_theorem_iInter n hA_compact hA_decreasing Hrel Γsec jMap
    cd.colH cd.colΓ cd.hjMap_ρ cd.hjMap_φ hsat
/-- **Lemma 32.4-style auxiliary.** Any compact subset `A` of a
topological `n`-manifold can be covered by finitely many closed sets
`D i`, each contained in the source of an atlas chart. This is the
reduction step that brings the proof of Theorem 32.1 to the
Euclidean-chart base case. -/

end OrientationTheorem

/--
[compact_subset_complement_eventually_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section32.lean)
-/
@[path]
private lemma compact_subset_complement_eventually_aux_eq
  [TopologicalSpace M]
  [TopologicalSpace X]
  {A : ℕ → Set X}
  {K : Set X}
-- given
  (hA_closed : ∀ i, IsClosed (A i))
  (hA_decreasing : ∀ i, A (i + 1) ⊆ A i)
  (hK : IsCompact K)
  (hKA : K ⊆ (⋂ i, A i)ᶜ) :
-- imply
  ∃ i, K ⊆ (A i)ᶜ := by
-- proof
  apply OrientationTheorem.compact_subset_complement_eventually_aux A hA_closed hA_decreasing K hK hKA


-- created on 2026-10-23
