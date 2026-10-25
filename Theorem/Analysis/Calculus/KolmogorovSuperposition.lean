/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Topology.UnitInterval
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Bases
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.HeineCantor
import Def.Analysis.Calculus.KolmogorovSuperposition
open scoped BoundedContinuousFunction


lemma continuous_stepRamp (c a : ℕ → ℝ) (K : ℕ) : Continuous (stepRamp c a K) := by
  unfold stepRamp
  apply Continuous.add continuous_const
  apply continuous_finsetSum
  intro i _
  apply Continuous.mul continuous_const
  exact continuous_const.min (continuous_const.max (continuous_id'.sub continuous_const))

lemma stepRamp_eq_of_between (c a : ℕ → ℝ) (K k : ℕ) (z : ℝ)
    (hkK : k ≤ K)
    (hlo : ∀ i < k, a i + 1 ≤ z)
    (hhi : ∀ i, k ≤ i → i < K → z ≤ a i) :
    stepRamp c a K z = c k := by
  unfold stepRamp
  have hclamp_lo : ∀ i ∈ Finset.range K, i < k →
      min 1 (max 0 (z - a i)) = 1 := by
    intro i _ hi
    have h1 : 1 ≤ max 0 (z - a i) := by
      have : 1 ≤ z - a i := by linarith [hlo i hi]
      exact le_max_of_le_right this
    exact min_eq_left h1
  have hclamp_hi : ∀ i ∈ Finset.range K, k ≤ i →
      min 1 (max 0 (z - a i)) = 0 := by
    intro i hi_mem hi
    have hiK : i < K := Finset.mem_range.mp hi_mem
    have h1 : z - a i ≤ 0 := by
      by_cases hkk : k = i
      · subst hkk
        -- need z ≤ a k; from hhi with i=k if k<K, else k=K and i=K impossible
        have : z ≤ a k := by
          by_cases hkK' : k < K
          · exact hhi k le_rfl hkK'
          · have : k = K := by omega
            subst this
            -- i = K, but i < K contradiction; this branch impossible
            omega
        linarith
      · have hlt : k < i ∨ k = i := by omega
        rcases hlt with hlt | heq
        · have : z ≤ a i := hhi i (by omega) hiK
          linarith
        · omega
    have h2 : max 0 (z - a i) = 0 := max_eq_left (by linarith)
    rw [h2, min_eq_right (by norm_num : (0:ℝ) ≤ 1)]
  -- split sum range K = range k + rest
  have hA : ∑ i ∈ Finset.range k, (c (i + 1) - c i) * min 1 (max 0 (z - a i))
      = ∑ i ∈ Finset.range k, (c (i + 1) - c i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    rw [hclamp_lo i (Finset.mem_range.mpr (lt_of_lt_of_le hik hkK)) hik]
    ring
  have hB : ∑ i ∈ Finset.Ico k K, (c (i + 1) - c i) * min 1 (max 0 (z - a i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [hclamp_hi i (Finset.mem_range.mpr (by omega : i < K)) hi.1]
    ring
  have hsplit : ∑ i ∈ Finset.range K, (c (i + 1) - c i) * min 1 (max 0 (z - a i))
      = ∑ i ∈ Finset.range k, (c (i + 1) - c i) := by
    have h := Finset.sum_range_add_sum_Ico
      (fun i => (c (i + 1) - c i) * min 1 (max 0 (z - a i))) hkK
    rw [hA, hB, add_zero] at h
    exact h.symm
  rw [hsplit, Finset.sum_range_sub]
  ring

lemma stepRamp_mem_segment (c a : ℕ → ℝ) (K k : ℕ) (z : ℝ)
    (hkK : k < K)
    (hlo : ∀ i < k, a i + 1 ≤ z)
    (hmid_lo : a k ≤ z) (hmid_hi : z ≤ a k + 1)
    (hhi : ∀ i, k < i → i < K → z ≤ a i) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ stepRamp c a K z = c k + s * (c (k + 1) - c k) := by
  have hs_mem : 0 ≤ z - a k ∧ z - a k ≤ 1 := by constructor <;> linarith
  set s : ℝ := min 1 (max 0 (z - a k)) with hs_def
  have hs_eq : s = z - a k := by
    rw [hs_def, max_eq_right hs_mem.1, min_eq_right hs_mem.2]
  have hs0 : 0 ≤ s := by rw [hs_eq]; linarith
  have hs1 : s ≤ 1 := by rw [hs_eq]; linarith
  refine ⟨s, hs0, hs1, ?_⟩
  unfold stepRamp
  have hclamp_lo : ∀ i ∈ Finset.range K, i < k →
      min 1 (max 0 (z - a i)) = 1 := by
    intro i _ hi
    have h1 : 1 ≤ max 0 (z - a i) := by
      have : 1 ≤ z - a i := by linarith [hlo i hi]
      exact le_max_of_le_right this
    exact min_eq_left h1
  have hclamp_hi : ∀ i ∈ Finset.range K, k < i →
      min 1 (max 0 (z - a i)) = 0 := by
    intro i hi_mem hi
    have hiK : i < K := Finset.mem_range.mp hi_mem
    have h1 : z - a i ≤ 0 := by linarith [hhi i hi hiK]
    have h2 : max 0 (z - a i) = 0 := max_eq_left (by linarith)
    rw [h2, min_eq_right (by norm_num : (0:ℝ) ≤ 1)]
  have hpart : Finset.range K = Finset.range k ∪ ({k} ∪ Finset.Ico (k + 1) K) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, Finset.mem_Ico]
    omega
  have hdisj1 : Disjoint (Finset.range k) ({k} ∪ Finset.Ico (k + 1) K) := by
    rw [Finset.disjoint_left]
    intro x hx
    simp only [Finset.mem_range] at hx
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Ico]
    omega
  have hdisj2 : Disjoint ({k} : Finset ℕ) (Finset.Ico (k + 1) K) := by
    rw [Finset.disjoint_left]
    intro x hx
    simp only [Finset.mem_singleton] at hx
    simp only [Finset.mem_Ico]
    omega
  have hA : ∑ i ∈ Finset.range k, (c (i + 1) - c i) * min 1 (max 0 (z - a i))
      = ∑ i ∈ Finset.range k, (c (i + 1) - c i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    have hikK : i < K := by omega
    rw [hclamp_lo i (Finset.mem_range.mpr hikK) hik]
    ring
  have hmid : ∑ x ∈ ({k} : Finset ℕ), (c (x + 1) - c x) * min 1 (max 0 (z - a x))
      = (c (k + 1) - c k) * s := by
    simp only [Finset.sum_singleton, hs_def]
  have htail : ∑ i ∈ Finset.Ico (k + 1) K, (c (i + 1) - c i) * min 1 (max 0 (z - a i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hiK : i < K := hi.2
    rw [hclamp_hi i (Finset.mem_range.mpr hiK) hi.1]
    ring
  have hsplit : ∑ i ∈ Finset.range K, (c (i + 1) - c i) * min 1 (max 0 (z - a i))
      = (∑ i ∈ Finset.range k, (c (i + 1) - c i)) + (c (k + 1) - c k) * s := by
    rw [hpart, Finset.sum_union hdisj1, Finset.sum_union hdisj2, hA, hmid, htail, add_zero]
  rw [hsplit, Finset.sum_range_sub]
  ring

lemma stepRamp_abs_le_max (c : ℕ → ℝ) (k : ℕ) (v y : ℝ)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hv : v = c k + s * (c (k + 1) - c k)) :
    |v - y| ≤ max |c k - y| |c (k + 1) - y| := by
  have h1s : 0 ≤ 1 - s := by linarith
  have hdecomp : v - y = (1 - s) * (c k - y) + s * (c (k + 1) - y) := by
    rw [hv]; ring
  rw [hdecomp]
  calc |(1 - s) * (c k - y) + s * (c (k + 1) - y)|
      ≤ (1 - s) * |c k - y| + s * |c (k + 1) - y| := by
        have h := abs_add_le ((1 - s) * (c k - y)) (s * (c (k + 1) - y))
        rwa [abs_mul, abs_mul, abs_of_nonneg h1s, abs_of_nonneg hs0] at h
    _ ≤ (1 - s) * max |c k - y| |c (k + 1) - y| + s * max |c k - y| |c (k + 1) - y| := by
        gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _
    _ = max |c k - y| |c (k + 1) - y| := by ring

lemma exists_small_injective_perturbation {Q J : Type*} [Finite Q] [Finite J]
    (A : Q → J → ℝ) (E : J → ℕ) (hE : Function.Injective E)
    {η₀ : ℝ} (hη₀ : 0 < η₀) :
    ∃ η, 0 < η ∧ η < η₀ ∧ ∀ q, Function.Injective (fun j => A q j + η * (E j : ℝ)) := by
  have := Fintype.ofFinite (Q × J × J)
  let B : Finset ℝ := Finset.univ.image (fun p : Q × J × J =>
    (A p.1 p.2.2 - A p.1 p.2.1) / ((E p.2.1 : ℝ) - E p.2.2))
  have hinf : (Set.Ioo 0 η₀).Infinite := Set.Ioo_infinite hη₀
  obtain ⟨η, hηmem, hηnot⟩ := hinf.exists_notMem_finset B
  refine ⟨η, hηmem.1, hηmem.2, fun q j j' h => ?_⟩
  by_contra hne
  have hEj : (E j : ℝ) ≠ E j' := by
    exact_mod_cast hE.ne hne
  have hηeq : η = (A q j' - A q j) / ((E j : ℝ) - E j') := by
    field_simp
    linarith [h]
  have hmem : η ∈ B := by
    simp only [B, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨(q, j, j'), hηeq.symm⟩
  exact hηnot hmem

lemma exists_bcf_interpolate {J : Type*} [Finite J]
    (v : J → ℝ) (hv : Function.Injective v) (y : J → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hy : ∀ j, |y j| ≤ B) :
    ∃ g : BoundedContinuousFunction ℝ ℝ, ‖g‖ ≤ B ∧ ∀ j, g (v j) = y j := by
  classical
  let S : Set ℝ := Set.range v
  have hSfin : S.Finite := Set.finite_range v
  have hSclosed : IsClosed S := hSfin.isClosed
  let e : J ≃ S := Equiv.ofInjective v hv
  let F : S → ℝ := fun s => y (e.symm s)
  have hFcont : Continuous F := continuous_of_discreteTopology
  let Fb : C(S, ℝ) := ⟨F, hFcont⟩
  let F₀ : BoundedContinuousFunction S ℝ := BoundedContinuousFunction.mkOfCompact Fb
  have hF₀norm : ‖F₀‖ ≤ B := by
    rw [BoundedContinuousFunction.norm_le hB]
    intro s
    rw [Real.norm_eq_abs, BoundedContinuousFunction.mkOfCompact_apply]
    obtain ⟨j, hj⟩ := e.surjective s
    subst hj
    change |F (e j)| ≤ B
    change |y (e.symm (e j))| ≤ B
    rw [Equiv.symm_apply_apply]
    exact hy j
  obtain ⟨g, hg_norm, hg_eq⟩ :=
    BoundedContinuousFunction.exists_extension_norm_eq_of_isClosedEmbedding F₀
      (IsClosed.isClosedEmbedding_subtypeVal hSclosed)
  refine ⟨g, hg_norm ▸ hF₀norm, fun j => ?_⟩
  have h := congrFun hg_eq (e j)
  simp only [Function.comp_apply] at h
  have hval : (((e j : S)) : ℝ) = v j := rfl
  rw [hval] at h
  rw [h]
  change (BoundedContinuousFunction.mkOfCompact Fb) (e j) = y j
  rw [BoundedContinuousFunction.mkOfCompact_apply]
  change F (e j) = y j
  change y (e.symm (e j)) = y j
  rw [Equiv.symm_apply_apply]

lemma abs_sub_sum_le_of_good {n : ℕ} {Q : Type*} [Fintype Q]
    (hQ : Fintype.card Q = 2 * n + 1)
    (G : Finset Q) (hG : n + 1 ≤ G.card)
    (M η F : ℝ) (hη : 0 ≤ η) (hF : |F| ≤ M)
    (a : Q → ℝ)
    (hgood : ∀ q ∈ G, |a q - F / (n + 1)| ≤ η / (n + 1))
    (hbound : ∀ q, |a q| ≤ M / (n + 1)) :
    |F - ∑ q, a q| ≤ n * M / (n + 1) + (2 * n + 1) * η / (n + 1) := by
  classical
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn1' : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  -- card bounds as reals
  have hcardQ : (Finset.univ (α := Q)).card = 2 * n + 1 := by rw [Finset.card_univ, hQ]
  have hGsub : G.card ≤ 2 * n + 1 := by rw [← hcardQ]; exact Finset.card_le_univ G
  have hk_le : (G.card : ℝ) ≤ 2 * (n : ℝ) + 1 := by exact_mod_cast hGsub
  have hk_ge : ((n : ℝ) + 1) ≤ (G.card : ℝ) := by
    have : (n + 1 : ℕ) ≤ G.card := hG
    calc ((n : ℝ) + 1) = (((n + 1 : ℕ)) : ℝ) := by push_cast; ring
      _ ≤ (G.card : ℝ) := by exact_mod_cast this
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg F) hF
  have hdivM : 0 ≤ M / (n + 1) := by positivity
  have hdivη : 0 ≤ η / (n + 1) := by positivity
  -- split the sum
  have hsplit : ∑ q, a q = ∑ q ∈ G, a q + ∑ q ∈ Gᶜ, a q := by
    rw [← Finset.sum_add_sum_compl G (fun q => a q)]
  -- key algebraic identity
  have hid : F - ∑ q, a q =
      F * (1 - (G.card : ℝ) / ((n : ℝ) + 1))
      - (∑ q ∈ G, (a q - F / ((n : ℝ) + 1)))
      - (∑ q ∈ Gᶜ, a q) := by
    rw [hsplit]
    have hsumF : ∑ _q ∈ G, (F / ((n : ℝ) + 1)) = (G.card : ℝ) * (F / ((n : ℝ) + 1)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    -- rewrite sums
    have hsub : (∑ q ∈ G, (a q - F / ((n : ℝ) + 1)))
        = (∑ q ∈ G, a q) - (G.card : ℝ) * (F / ((n : ℝ) + 1)) := by
      rw [Finset.sum_sub_distrib, hsumF]
    rw [hsub]
    have hmul : F * ((G.card : ℝ) / ((n : ℝ) + 1))
        = (G.card : ℝ) * (F / ((n : ℝ) + 1)) := by ring
    have hexpand : F * (1 - (G.card : ℝ) / ((n : ℝ) + 1))
        = F - F * ((G.card : ℝ) / ((n : ℝ) + 1)) := by ring
    rw [hexpand, hmul]
    ring
  rw [hid]
  -- triangle inequality
  have htri : |F * (1 - (G.card : ℝ) / ((n : ℝ) + 1))
      - (∑ q ∈ G, (a q - F / ((n : ℝ) + 1)))
      - (∑ q ∈ Gᶜ, a q)|
      ≤ |F * (1 - (G.card : ℝ) / ((n : ℝ) + 1))|
        + |∑ q ∈ G, (a q - F / ((n : ℝ) + 1))|
        + |∑ q ∈ Gᶜ, a q| := by
    have hA : |(F * (1 - (G.card : ℝ) / ((n : ℝ) + 1))
        - (∑ q ∈ G, (a q - F / ((n : ℝ) + 1)))) - (∑ q ∈ Gᶜ, a q)|
        ≤ |F * (1 - (G.card : ℝ) / ((n : ℝ) + 1))
          - (∑ q ∈ G, (a q - F / ((n : ℝ) + 1)))| + |∑ q ∈ Gᶜ, a q| := by
      have h := abs_sub_le (F * (1 - (G.card : ℝ) / ((n : ℝ) + 1))
        - (∑ q ∈ G, (a q - F / ((n : ℝ) + 1)))) 0 (∑ q ∈ Gᶜ, a q)
      simp only [sub_zero, zero_sub, abs_neg] at h
      exact h
    have hB : |F * (1 - (G.card : ℝ) / ((n : ℝ) + 1))
        - (∑ q ∈ G, (a q - F / ((n : ℝ) + 1)))|
        ≤ |F * (1 - (G.card : ℝ) / ((n : ℝ) + 1))|
          + |∑ q ∈ G, (a q - F / ((n : ℝ) + 1))| := by
      have h := abs_sub_le (F * (1 - (G.card : ℝ) / ((n : ℝ) + 1))) 0
        (∑ q ∈ G, (a q - F / ((n : ℝ) + 1)))
      simp only [sub_zero, zero_sub, abs_neg] at h
      exact h
    exact le_trans hA (by linarith [hB])
  refine le_trans htri ?_
  -- bound each piece
  have h1 : |F * (1 - (G.card : ℝ) / ((n : ℝ) + 1))|
      ≤ M * ((G.card : ℝ) - ((n : ℝ) + 1)) / ((n : ℝ) + 1) := by
    rw [abs_mul]
    have hF' : |F| ≤ M := hF
    have hge1 : (1 : ℝ) ≤ (G.card : ℝ) / ((n : ℝ) + 1) := by
      rw [le_div_iff₀ hn1]
      linarith [hk_ge]
    have habs : |1 - (G.card : ℝ) / ((n : ℝ) + 1)|
        = ((G.card : ℝ) - ((n : ℝ) + 1)) / ((n : ℝ) + 1) := by
      rw [abs_sub_comm, abs_of_nonneg]
      · field_simp
      · linarith [hge1]
    rw [habs, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hF'
      (by positivity : (0:ℝ) ≤ ((G.card : ℝ) - ((n : ℝ) + 1)) / ((n : ℝ) + 1))
  have h2 : |∑ q ∈ G, (a q - F / ((n : ℝ) + 1))| ≤ (G.card : ℝ) * (η / ((n : ℝ) + 1)) := by
    calc |∑ q ∈ G, (a q - F / ((n : ℝ) + 1))|
        ≤ ∑ q ∈ G, |a q - F / ((n : ℝ) + 1)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _q ∈ G, (η / ((n : ℝ) + 1)) := by
          apply Finset.sum_le_sum
          intro q hq
          have := hgood q hq
          -- convert F/(n+1 : ℕ) vs F/((n:ℝ)+1): they are equal by cast
          simpa using this
      _ = (G.card : ℝ) * (η / ((n : ℝ) + 1)) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcompl : (Gᶜ.card : ℝ) = (2 * (n : ℝ) + 1) - (G.card : ℝ) := by
    have hcc : Gᶜ.card = Fintype.card Q - G.card := Finset.card_compl G
    rw [hcc, hQ]
    rw [Nat.cast_sub (by omega : G.card ≤ 2 * n + 1)]
    push_cast
    ring
  have h3 : |∑ q ∈ Gᶜ, a q| ≤ ((2 * (n : ℝ) + 1) - (G.card : ℝ)) * (M / ((n : ℝ) + 1)) := by
    calc |∑ q ∈ Gᶜ, a q| ≤ ∑ q ∈ Gᶜ, |a q| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _q ∈ Gᶜ, (M / ((n : ℝ) + 1)) := by
          apply Finset.sum_le_sum
          intro q _
          have := hbound q
          simpa using this
      _ = (Gᶜ.card : ℝ) * (M / ((n : ℝ) + 1)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((2 * (n : ℝ) + 1) - (G.card : ℝ)) * (M / ((n : ℝ) + 1)) := by rw [hcompl]
  -- combine: M-terms telescope to n*M/(n+1), η-term bounded by (2n+1)*η/(n+1)
  have h2' : (G.card : ℝ) * (η / ((n : ℝ) + 1)) ≤ (2 * (n : ℝ) + 1) * (η / ((n : ℝ) + 1)) := by
    apply mul_le_mul_of_nonneg_right hk_le (by positivity)
  calc |F * (1 - ↑G.card / (↑n + 1))| + |∑ q ∈ G, (a q - F / (↑n + 1))| + |∑ q ∈ Gᶜ, a q|
      ≤ M * ((G.card : ℝ) - ((n : ℝ) + 1)) / ((n : ℝ) + 1)
        + (G.card : ℝ) * (η / ((n : ℝ) + 1))
        + ((2 * (n : ℝ) + 1) - (G.card : ℝ)) * (M / ((n : ℝ) + 1)) := by gcongr
    _ ≤ n * M / (n + 1) + (2 * n + 1) * η / (n + 1) := by
        have hN : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        -- normalize divisions
        field_simp
        nlinarith [hk_ge, hk_le, hM_nonneg, hη, sq_nonneg ((G.card : ℝ) - ((n : ℝ) + 1))]

