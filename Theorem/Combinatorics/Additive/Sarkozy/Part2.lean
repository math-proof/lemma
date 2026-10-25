/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Data.Finset.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Tactic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.Data.Finsupp.Basic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Module.Basic
import Def.Combinatorics.Additive.Sarkozy.Part2


namespace MathlibExt.Combinatorics.Additive.SarkozyWanted

open scoped InnerProductSpace

/-- Each correlation count as a sum of indicators over the product. -/
theorem sarkozyCorr_eq_sum (A : Set ℕ) (N : ℕ) {ι : Type*} (e : ι → ℤ)
    (i j : ι) :
    ((sarkozyCorr A N (e i - e j) : ℕ) : ℝ)
      = ∑ x ∈ (sarkozyFin A N) ×ˢ (sarkozyFin A N),
        (if (x.1 : ℤ) - (x.2 : ℤ) = e i - e j then (1 : ℝ) else 0) := by
  simp only [sarkozyCorr, ← Finset.sum_boole]

/-- The fiber weight as a single sum over the product. -/
theorem sarkozyW_eq_sum {ι : Type*} (A : Set ℕ) (N : ℕ) (s : Finset ι)
    (e : ι → ℤ) (c : ι → ℝ) (t : ℤ) :
    sarkozyW A N s e c t
      = ∑ x ∈ (sarkozyFin A N) ×ˢ s,
        (if (x.1 : ℤ) - e x.2 = t then c x.2 else 0) := by
  simp only [sarkozyW, Finset.sum_product]

/-- Left-hand side of the identity as a four-fold sum. -/
theorem sarkozyLHS_eq {ι : Type*} (A : Set ℕ) (N : ℕ) (s : Finset ι)
    (e : ι → ℤ) (c : ι → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, c i * c j * ((sarkozyCorr A N (e i - e j) : ℕ) : ℝ))
      = ∑ i ∈ s, ∑ j ∈ s, ∑ a ∈ sarkozyFin A N, ∑ b ∈ sarkozyFin A N,
        (if (a : ℤ) - e i = (b : ℤ) - e j then c i * c j else 0) := by
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [sarkozyCorr_eq_sum A N e i j,
    Finset.mul_sum _ _ (c i * c j), Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : (a : ℤ) - (b : ℤ) = e i - e j
  · have h' : (a : ℤ) - e i = (b : ℤ) - e j :=
      sub_eq_sub_iff_sub_eq_sub.mp h
    simp [h, h']
  · have h' : ¬ ((a : ℤ) - e i = (b : ℤ) - e j) :=
      fun hh => h (sub_eq_sub_iff_sub_eq_sub.mpr hh)
    simp [h, h']

/-- The inner `t`-sum collapses to a single Kronecker term. -/
theorem sarkozyTsum_eq {ι : Type*} (A : Set ℕ) (N : ℕ) (s : Finset ι)
    (e : ι → ℤ) (c : ι → ℝ) (x y : ℕ × ι)
    (hx : x ∈ (sarkozyFin A N) ×ˢ s) :
    (∑ t ∈ sarkozyIm A N s e,
      ((if (x.1 : ℤ) - e x.2 = t then c x.2 else 0)
        * (if (y.1 : ℤ) - e y.2 = t then c y.2 else 0)))
    = (if (x.1 : ℤ) - e x.2 = (y.1 : ℤ) - e y.2 then c x.2 * c y.2 else 0) := by
  by_cases hxy : (x.1 : ℤ) - e x.2 = (y.1 : ℤ) - e y.2
  · have hmem : (x.1 : ℤ) - e x.2 ∈ sarkozyIm A N s e := by
      simp only [sarkozyIm, Finset.mem_image]
      exact ⟨x, hx, rfl⟩
    have hterm : ∀ t ∈ sarkozyIm A N s e,
        (if (x.1 : ℤ) - e x.2 = t then c x.2 else 0)
          * (if (y.1 : ℤ) - e y.2 = t then c y.2 else 0)
        = (if (x.1 : ℤ) - e x.2 = t then c x.2 * c y.2 else 0) := by
      intro t _
      rw [← hxy]
      by_cases h : (x.1 : ℤ) - e x.2 = t <;> simp [h]
    have hval : (∑ t ∈ sarkozyIm A N s e,
        ((if (x.1 : ℤ) - e x.2 = t then c x.2 else 0)
          * (if (y.1 : ℤ) - e y.2 = t then c y.2 else 0)))
        = c x.2 * c y.2 := by
      rw [(Finset.sum_congr rfl hterm), Finset.sum_ite_eq, ite_eq_left hmem]
    rw [hval, ite_eq_left hxy]
  · have hterm : ∀ t ∈ sarkozyIm A N s e,
        (if (x.1 : ℤ) - e x.2 = t then c x.2 else 0)
          * (if (y.1 : ℤ) - e y.2 = t then c y.2 else 0) = 0 := by
      intro t _
      by_cases h1 : (x.1 : ℤ) - e x.2 = t
      · by_cases h2 : (y.1 : ℤ) - e y.2 = t
        · exact absurd (h1.trans h2.symm) hxy
        · simp [h2]
      · simp [h1]
    have hzero : (∑ t ∈ sarkozyIm A N s e,
        ((if (x.1 : ℤ) - e x.2 = t then c x.2 else 0)
          * (if (y.1 : ℤ) - e y.2 = t then c y.2 else 0))) = 0 :=
      Finset.sum_eq_zero hterm
    rw [hzero, ite_eq_right hxy]

/-- Product sums unfold to iterated sums. -/
theorem sarkozyProd_eq {ι : Type*} (A : Set ℕ) (N : ℕ) (s : Finset ι)
    (G : (ℕ × ι) → (ℕ × ι) → ℝ) :
    (∑ x ∈ (sarkozyFin A N) ×ˢ s, ∑ y ∈ (sarkozyFin A N) ×ˢ s, G x y)
      = ∑ a ∈ sarkozyFin A N, ∑ i ∈ s, ∑ b ∈ sarkozyFin A N, ∑ j ∈ s,
        G (a, i) (b, j) := by
  simp only [Finset.sum_product]

/-- Right-hand side of the identity as a four-fold sum. -/
theorem sarkozyRHS_eq {ι : Type*} (A : Set ℕ) (N : ℕ) (s : Finset ι)
    (e : ι → ℤ) (c : ι → ℝ) :
    (∑ t ∈ sarkozyIm A N s e, (sarkozyW A N s e c t) ^ 2)
      = ∑ a ∈ sarkozyFin A N, ∑ i ∈ s, ∑ b ∈ sarkozyFin A N, ∑ j ∈ s,
        (if (a : ℤ) - e i = (b : ℤ) - e j then c i * c j else 0) := by
  have hexpand : ∀ t ∈ sarkozyIm A N s e,
      (sarkozyW A N s e c t) ^ 2
        = ∑ x ∈ (sarkozyFin A N) ×ˢ s, ∑ y ∈ (sarkozyFin A N) ×ˢ s,
          ((if (x.1 : ℤ) - e x.2 = t then c x.2 else 0)
            * (if (y.1 : ℤ) - e y.2 = t then c y.2 else 0)) := by
    intro t _
    rw [sarkozyW_eq_sum A N s e c t, pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    exact Finset.mul_sum _ _ _
  rw [Finset.sum_congr rfl hexpand]
  trans ∑ x ∈ (sarkozyFin A N) ×ˢ s, ∑ y ∈ (sarkozyFin A N) ×ˢ s,
    ∑ t ∈ sarkozyIm A N s e,
      ((if (x.1 : ℤ) - e x.2 = t then c x.2 else 0)
        * (if (y.1 : ℤ) - e y.2 = t then c y.2 else 0))
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    exact Finset.sum_comm
  · rw [Finset.sum_congr rfl (fun x hx =>
      Finset.sum_congr rfl (fun y _ => sarkozyTsum_eq A N s e c x y hx))]
    exact sarkozyProd_eq A N s _

/-- The correlation sum-of-squares identity (N1). -/
theorem sarkozy_corr_sum_sq_identity {ι : Type*} (A : Set ℕ) (N : ℕ)
    (s : Finset ι) (e : ι → ℤ) (c : ι → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, c i * c j * ((sarkozyCorr A N (e i - e j) : ℕ) : ℝ))
      = ∑ t ∈ (sarkozyIm A N s e), (sarkozyW A N s e c t) ^ 2 := by
  have step1 : (∑ i ∈ s, ∑ j ∈ s, ∑ a ∈ sarkozyFin A N, ∑ b ∈ sarkozyFin A N,
        (if (a : ℤ) - e i = (b : ℤ) - e j then c i * c j else 0))
      = ∑ i ∈ s, ∑ a ∈ sarkozyFin A N, ∑ j ∈ s, ∑ b ∈ sarkozyFin A N,
        (if (a : ℤ) - e i = (b : ℤ) - e j then c i * c j else 0) :=
    Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
  have step2 : (∑ i ∈ s, ∑ a ∈ sarkozyFin A N, ∑ j ∈ s, ∑ b ∈ sarkozyFin A N,
        (if (a : ℤ) - e i = (b : ℤ) - e j then c i * c j else 0))
      = ∑ a ∈ sarkozyFin A N, ∑ i ∈ s, ∑ j ∈ s, ∑ b ∈ sarkozyFin A N,
        (if (a : ℤ) - e i = (b : ℤ) - e j then c i * c j else 0) :=
    Finset.sum_comm
  have step3 : (∑ a ∈ sarkozyFin A N, ∑ i ∈ s, ∑ j ∈ s, ∑ b ∈ sarkozyFin A N,
        (if (a : ℤ) - e i = (b : ℤ) - e j then c i * c j else 0))
      = ∑ a ∈ sarkozyFin A N, ∑ i ∈ s, ∑ b ∈ sarkozyFin A N, ∑ j ∈ s,
        (if (a : ℤ) - e i = (b : ℤ) - e j then c i * c j else 0) :=
    Finset.sum_congr rfl
      (fun a _ => Finset.sum_congr rfl (fun i _ => Finset.sum_comm))
  rw [sarkozyLHS_eq A N s e c, step1, step2, step3, sarkozyRHS_eq A N s e c]

/-- Positive semidefiniteness of the finite correlations (N1 consequence). -/
theorem sarkozy_corr_nonneg {ι : Type*} (A : Set ℕ) (N : ℕ) (s : Finset ι)
    (e : ι → ℤ) (c : ι → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * ((sarkozyCorr A N (e i - e j) : ℕ) : ℝ) := by
  rw [sarkozy_corr_sum_sq_identity A N s e c]
  exact Finset.sum_nonneg (fun t _ => sq_nonneg _)

/-- Correlations are even (N2a). -/
theorem sarkozy_corr_neg (A : Set ℕ) (N : ℕ) (d : ℤ) :
    sarkozyCorr A N (-d) = sarkozyCorr A N d := by
  simp only [sarkozyCorr]
  apply Finset.card_bij (fun p _ => p.swap)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Prod.fst_swap,
      Prod.snd_swap] at hp ⊢
    obtain ⟨⟨ha, hb⟩, h⟩ := hp
    exact ⟨⟨hb, ha⟩, by omega⟩
  · intro a₁ _ a₂ _ h
    simpa using congrArg Prod.swap h
  · intro b hb
    rw [Finset.mem_filter] at hb
    obtain ⟨hmem, h⟩ := hb
    rw [Finset.mem_product] at hmem
    refine ⟨b.swap, ?_, Prod.swap_swap b⟩
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_product]
      simp only [Prod.fst_swap, Prod.snd_swap]
      exact ⟨hmem.2, hmem.1⟩
    · simp only [Prod.fst_swap, Prod.snd_swap]
      omega

/-- Correlations are bounded by the initial segment count (N2b). -/
theorem sarkozy_corr_le_card (A : Set ℕ) (N : ℕ) (d : ℤ) :
    sarkozyCorr A N d ≤ (sarkozyFin A N).card := by
  simp only [sarkozyCorr]
  apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.1)
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
    simp only [Finset.mem_coe]
    exact hp.1.1
  · intro p hp q hq h
    simp only [Finset.mem_coe, Finset.mem_filter] at hp hq
    obtain ⟨_, hp2⟩ := hp
    obtain ⟨_, hq2⟩ := hq
    have h1 : p.1 = q.1 := h
    have h2 : p.2 = q.2 := by omega
    exact Prod.ext h1 h2

/-- The initial segment count is bounded by `N` (N2b). -/
theorem sarkozy_card_le (A : Set ℕ) (N : ℕ) :
    (sarkozyFin A N).card ≤ N := by
  have hsub : sarkozyFin A N ⊆ Finset.range N := by
    intro n hn
    exact (sarkozyFin_mem A N n |>.mp hn).1
  calc (sarkozyFin A N).card ≤ (Finset.range N).card := Finset.card_le_card hsub
    _ = N := Finset.card_range N

/-- Correlations vanish at positive squares under NSD (N2c). -/
theorem sarkozy_corr_sq_eq_zero (A : Set ℕ) (N : ℕ) (k : ℕ) (hk : 0 < k)
    (hNSD : ∀ a b k : ℕ, a ∈ A → b ∈ A → 0 < k → a < b → b ≠ a + k * k) :
    sarkozyCorr A N ((k : ℤ) * k) = 0 := by
  simp only [sarkozyCorr]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp
  simp only [Finset.mem_product] at hp
  obtain ⟨ha, hb⟩ := hp
  rw [sarkozyFin_mem] at ha hb
  intro hcon
  have hpos : (0 : ℤ) < (k : ℤ) * k :=
    mul_pos (by exact_mod_cast hk) (by exact_mod_cast hk)
  have hlt : p.2 < p.1 := by omega
  have heq : p.1 = p.2 + k * k := by
    have hcast : ((p.1 : ℕ) : ℤ) = ((p.2 + k * k : ℕ) : ℤ) := by
      push_cast
      omega
    exact Nat.cast_injective hcast
  exact hNSD p.2 p.1 k hb.2 ha.2 hk hlt heq

/-- Total fiber weight for the Fejér bound (N3 helper). -/
theorem sarkozyW_tot (A : Set ℕ) (N L : ℕ) :
    (∑ t ∈ sarkozyIm A N (Finset.range L) (fun i => (i : ℤ)),
      sarkozyW A N (Finset.range L) (fun i => (i : ℤ)) (fun _ => 1) t)
      = (L : ℝ) * ((sarkozyFin A N).card : ℝ) := by
  have h1 : (∑ t ∈ sarkozyIm A N (Finset.range L) (fun i => (i : ℤ)),
        sarkozyW A N (Finset.range L) (fun i => (i : ℤ)) (fun _ => 1) t)
      = ∑ a ∈ sarkozyFin A N, ∑ h ∈ Finset.range L,
        ∑ t ∈ sarkozyIm A N (Finset.range L) (fun i => (i : ℤ)),
          (if (a : ℤ) - (h : ℤ) = t then (1 : ℝ) else 0) := by
    simp only [sarkozyW]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    exact Finset.sum_comm
  rw [h1]
  have h2 : ∀ a ∈ sarkozyFin A N, ∀ h ∈ Finset.range L,
      (∑ t ∈ sarkozyIm A N (Finset.range L) (fun i => (i : ℤ)),
        (if (a : ℤ) - (h : ℤ) = t then (1 : ℝ) else 0)) = 1 := by
    intro a ha h hh
    rw [Finset.sum_ite_eq]
    have hmem : (a : ℤ) - (h : ℤ)
        ∈ sarkozyIm A N (Finset.range L) (fun i => (i : ℤ)) := by
      simp only [sarkozyIm, Finset.mem_image]
      exact ⟨(a, h), Finset.mk_mem_product ha hh, rfl⟩
    rw [ite_eq_left hmem]
  rw [Finset.sum_congr rfl (fun a ha =>
    Finset.sum_congr rfl (fun h hh => h2 a ha h hh))]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  ring

/-- The fiber image lies in an integer interval (N3 helper). -/
theorem sarkozyIm_sub (A : Set ℕ) (N L : ℕ) :
    sarkozyIm A N (Finset.range L) (fun i => (i : ℤ))
      ⊆ Finset.Ioo (-(L : ℤ)) (N : ℤ) := by
  intro t ht
  simp only [sarkozyIm, Finset.mem_image, Finset.mem_product] at ht
  obtain ⟨⟨a, h⟩, ⟨ha, hh⟩, rfl⟩ := ht
  have ha' : a ∈ sarkozyFin A N := ha
  have hh' : h ∈ Finset.range L := hh
  rw [sarkozyFin_mem, Finset.mem_range] at ha'
  rw [Finset.mem_range] at hh'
  simp only [Finset.mem_Ioo]
  constructor <;> omega

/-- Cardinality bound for the fiber image (N3 helper). -/
theorem sarkozyIm_card (A : Set ℕ) (N L : ℕ) :
    (sarkozyIm A N (Finset.range L) (fun i => (i : ℤ))).card ≤ N + L := by
  calc (sarkozyIm A N (Finset.range L) (fun i => (i : ℤ))).card
      ≤ (Finset.Ioo (-(L : ℤ)) (N : ℤ)).card :=
        Finset.card_le_card (sarkozyIm_sub A N L)
    _ = (((N : ℤ) - (-(L : ℤ)) - 1).toNat) := Int.card_Ioo _ _
    _ ≤ (((N + L : ℕ) : ℤ)).toNat := by
        apply Int.toNat_le_toNat
        push_cast
        omega
    _ = N + L := Int.toNat_natCast (N + L)

/-- Fejér lower bound for the finite correlations (N3). -/
theorem sarkozy_corr_fejer_lower_bound (A : Set ℕ) (N L : ℕ) :
    (L : ℝ) ^ 2 * ((sarkozyFin A N).card : ℝ) ^ 2
      ≤ ((N : ℝ) + L) * (∑ h ∈ Finset.range L, ∑ h' ∈ Finset.range L,
        ((sarkozyCorr A N ((h : ℤ) - h') : ℕ) : ℝ)) := by
  have hN1 := sarkozy_corr_sum_sq_identity A N (Finset.range L)
    (fun i => (i : ℤ)) (fun _ => 1)
  have hSeq : (∑ h ∈ Finset.range L, ∑ h' ∈ Finset.range L,
        ((sarkozyCorr A N ((h : ℤ) - h') : ℕ) : ℝ))
      = ∑ t ∈ sarkozyIm A N (Finset.range L) (fun i => (i : ℤ)),
        (sarkozyW A N (Finset.range L) (fun i => (i : ℤ)) (fun _ => 1) t) ^ 2 := by
    simpa using hN1
  have hCS := sq_sum_le_card_mul_sum_sq
    (s := sarkozyIm A N (Finset.range L) (fun i => (i : ℤ)))
    (f := sarkozyW A N (Finset.range L) (fun i => (i : ℤ)) (fun _ => 1))
  rw [sarkozyW_tot A N L] at hCS
  have hcardR : ((sarkozyIm A N (Finset.range L) (fun i => (i : ℤ))).card : ℝ)
      ≤ (N : ℝ) + (L : ℝ) := by
    have h := sarkozyIm_card A N L
    have h2 : ((sarkozyIm A N (Finset.range L) (fun i => (i : ℤ))).card : ℝ)
        ≤ ((N + L : ℕ) : ℝ) := by
      exact_mod_cast h
    rwa [Nat.cast_add] at h2
  have hG2nn : 0 ≤ ∑ t ∈ sarkozyIm A N (Finset.range L) (fun i => (i : ℤ)),
      (sarkozyW A N (Finset.range L) (fun i => (i : ℤ)) (fun _ => 1) t) ^ 2 :=
    Finset.sum_nonneg (fun t _ => sq_nonneg _)
  rw [hSeq]
  calc (L : ℝ) ^ 2 * ((sarkozyFin A N).card : ℝ) ^ 2
        = ((L : ℝ) * ((sarkozyFin A N).card : ℝ)) ^ 2 := by ring
    _ ≤ ((sarkozyIm A N (Finset.range L) (fun i => (i : ℤ))).card : ℝ) *
        (∑ t ∈ sarkozyIm A N (Finset.range L) (fun i => (i : ℤ)),
          (sarkozyW A N (Finset.range L) (fun i => (i : ℤ)) (fun _ => 1) t) ^ 2) :=
        hCS
    _ ≤ ((N : ℝ) + (L : ℝ)) *
        (∑ t ∈ sarkozyIm A N (Finset.range L) (fun i => (i : ℤ)),
          (sarkozyW A N (Finset.range L) (fun i => (i : ℤ)) (fun _ => 1) t) ^ 2) :=
        mul_le_mul_of_nonneg_right hcardR hG2nn

end MathlibExt.Combinatorics.Additive.SarkozyWanted
