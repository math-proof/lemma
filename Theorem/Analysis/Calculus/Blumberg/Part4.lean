import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Data.Int.Star
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.UniformSpace.Uniformizable
import Def.Analysis.Calculus.Blumberg.Part3


section

namespace MetaMathlibExt

-- N5e: dyadics are countable.
theorem blum_dyadic_countable : blumDyadic.Countable := by
  have hEq : blumDyadic =
      Set.range (fun p : ℕ × ℤ => ((p.2 : ℝ) / 2 ^ p.1)) := by
    ext x
    constructor
    · intro h
      have h' : ∃ m : ℕ, ∃ a : ℤ, x = (a : ℝ) / 2 ^ m := h
      obtain ⟨m, a, rfl⟩ := h'
      exact ⟨(m, a), rfl⟩
    · intro h
      obtain ⟨⟨m, a⟩, rfl⟩ := h
      exact ⟨m, a, rfl⟩
  rw [hEq]
  exact Set.countable_range _

-- N5c: non-dyadic points lie in their floor dyadic interval.
theorem blum_mem_dyI_floor (m : ℕ) {x : ℝ} (hx : x ∉ blumDyadic) :
    x ∈ blumDyI m ⌊x * 2 ^ m⌋ := by
  have h2pos : (0 : ℝ) < 2 ^ m := by positivity
  have hfle : (⌊x * 2 ^ m⌋ : ℝ) ≤ x * 2 ^ m := Int.floor_le _
  have hflt : x * 2 ^ m < (⌊x * 2 ^ m⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hlt : (⌊x * 2 ^ m⌋ : ℝ) < x * 2 ^ m := by
    by_contra h
    have hle : x * 2 ^ m ≤ (⌊x * 2 ^ m⌋ : ℝ) := le_of_not_gt h
    have heq : x * 2 ^ m = (⌊x * 2 ^ m⌋ : ℝ) := le_antisymm hle hfle
    have heq2 : x = ((⌊x * 2 ^ m⌋ : ℝ)) / 2 ^ m := by
      rw [eq_div_iff (ne_of_gt h2pos)]
      exact heq
    apply hx
    change ∃ mm : ℕ, ∃ aa : ℤ, x = (aa : ℝ) / 2 ^ mm
    exact ⟨m, ⌊x * 2 ^ m⌋, heq2⟩
  rw [blumDyI]
  rw [Set.mem_Ioo]
  constructor
  · rw [div_lt_iff₀ h2pos]
    linarith [hlt]
  · rw [lt_div_iff₀ h2pos]
    linarith [hflt]

-- N5d: a dyadic interval sits in a small ball around any of its points.
theorem blum_dyI_subset_ball (m : ℕ) (a : ℤ) {x : ℝ}
    (hx : x ∈ blumDyI m a) : blumDyI m a ⊆ Metric.ball x (1 / 2 ^ m) := by
  have h2pos : (0 : ℝ) < 2 ^ m := by positivity
  have hlen : (((a : ℝ) + 1) / 2 ^ m) - ((a : ℝ) / 2 ^ m) = 1 / 2 ^ m := by
    field_simp
    ring
  have hx' : (a : ℝ) / 2 ^ m < x ∧ x < ((a : ℝ) + 1) / 2 ^ m := by
    simpa [blumDyI] using hx
  intro y hy
  have hy' : (a : ℝ) / 2 ^ m < y ∧ y < ((a : ℝ) + 1) / 2 ^ m := by
    simpa [blumDyI] using hy
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hx'.1, hx'.2, hy'.1, hy'.2, hlen]

theorem blumDyI_mem_iff (m : ℕ) (a : ℤ) (x : ℝ) :
    x ∈ blumDyI m a ↔ (a : ℝ) < x * 2 ^ m ∧ x * 2 ^ m < (a : ℝ) + 1 := by
  have h2pos : (0 : ℝ) < 2 ^ m := by positivity
  rw [blumDyI, Set.mem_Ioo, div_lt_iff₀ h2pos, lt_div_iff₀ h2pos]

theorem blum_dyI_laminar {m m' : ℕ} {a a' : ℤ} (hle : m ≤ m')
    (hne : (blumDyI m' a' ∩ blumDyI m a).Nonempty) :
    blumDyI m' a' ⊆ blumDyI m a := by
  obtain ⟨z, hz1, hz2⟩ := hne
  have hz1' := (blumDyI_mem_iff m' a' z).mp hz1
  have hz2' := (blumDyI_mem_iff m a z).mp hz2
  set j := m' - m with hj
  have hm' : m' = m + j := (Nat.add_sub_cancel' hle).symm
  have hPpos : (0 : ℤ) < 2 ^ j := pow_pos (by norm_num) _
  have hPne : (2 : ℤ) ^ j ≠ 0 := ne_of_gt hPpos
  set b := a' / 2 ^ j with hb
  have h1 : b * 2 ^ j ≤ a' := Int.ediv_mul_le _ hPne
  have h2 : a' < (b + 1) * 2 ^ j := Int.lt_ediv_add_one_mul_self _ hPpos
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have c1 : (b : ℝ) * 2 ^ j ≤ (a' : ℝ) := by
    have h : ((b * 2 ^ j : ℤ) : ℝ) ≤ ((a' : ℤ) : ℝ) := Int.cast_le.mpr h1
    push_cast at h
    exact h
  have c2 : (a' : ℝ) < ((b : ℝ) + 1) * 2 ^ j := by
    have h : ((a' : ℤ) : ℝ) < ((((b + 1) * 2 ^ j : ℤ)) : ℝ) :=
      Int.cast_lt.mpr h2
    push_cast at h
    exact h
  have h3 : a' + 1 ≤ (b + 1) * 2 ^ j := by omega
  have c3 : (a' : ℝ) + 1 ≤ ((b : ℝ) + 1) * 2 ^ j := by
    have h : (((a' + 1 : ℤ)) : ℝ) ≤ ((((b + 1) * 2 ^ j : ℤ)) : ℝ) :=
      Int.cast_le.mpr h3
    push_cast at h
    exact h
  have hpow : (2 : ℝ) ^ m' = 2 ^ m * 2 ^ j := by rw [hm', pow_add]
  have sub1 : blumDyI m' a' ⊆ blumDyI m b := by
    intro y hy
    have hy' := (blumDyI_mem_iff m' a' y).mp hy
    rw [hpow] at hy'
    rw [blumDyI_mem_iff]
    constructor
    · have e3 : y * (2 ^ m * 2 ^ j) = (y * 2 ^ m) * 2 ^ j := by ring
      have hlt : (b : ℝ) * 2 ^ j < (y * 2 ^ m) * 2 ^ j := by
        rw [← e3]
        exact lt_of_le_of_lt c1 hy'.1
      exact lt_of_mul_lt_mul_right hlt (le_of_lt h2j)
    · have e3 : y * (2 ^ m * 2 ^ j) = (y * 2 ^ m) * 2 ^ j := by ring
      have hlt : (y * 2 ^ m) * 2 ^ j < ((b : ℝ) + 1) * 2 ^ j := by
        rw [← e3]
        exact lt_of_lt_of_le hy'.2 c3
      exact lt_of_mul_lt_mul_right hlt (le_of_lt h2j)
  have hzb := (blumDyI_mem_iff m b z).mp (sub1 hz1)
  have hba1 : b ≤ a := by
    have h : (b : ℝ) < (a : ℝ) + 1 := lt_trans hzb.1 hz2'.2
    have h' : b < a + 1 := by exact_mod_cast h
    omega
  have hba2 : a ≤ b := by
    have h : (a : ℝ) < (b : ℝ) + 1 := lt_trans hz2'.1 hzb.2
    have h' : a < b + 1 := by exact_mod_cast h
    omega
  have hba : b = a := le_antisymm hba1 hba2
  rw [hba] at sub1
  exact sub1

-- N5b: a dyadic interval cannot contain one of strictly smaller level.
theorem blum_dyI_not_subset_of_lt {m m' : ℕ} {a a' : ℤ} (hlt : m < m') :
    ¬ blumDyI m a ⊆ blumDyI m' a' := by
  intro hsub
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have h2m' : (0 : ℝ) < 2 ^ m' := by positivity
  have hlen : (((a : ℝ) + 1) / 2 ^ m) - ((a : ℝ) / 2 ^ m) = 1 / 2 ^ m := by
    field_simp
    ring
  have hlen' : (((a' : ℝ) + 1) / 2 ^ m') - ((a' : ℝ) / 2 ^ m') = 1 / 2 ^ m' := by
    field_simp
    ring
  set l : ℝ := (a : ℝ) / 2 ^ m with hl
  set r : ℝ := ((a : ℝ) + 1) / 2 ^ m with hr
  have hlr : l < r := by
    rw [hl, hr]
    have : (a : ℝ) / 2 ^ m < ((a : ℝ) + 1) / 2 ^ m := by
      apply div_lt_div_of_pos_right _ h2m
      linarith
    exact this
  set p : ℝ := l + (r - l) / 4 with hp
  set q : ℝ := l + 3 * (r - l) / 4 with hq
  have hplr : l < p ∧ p < r := by constructor <;> (rw [hp]; linarith)
  have hqlr : l < q ∧ q < r := by constructor <;> (rw [hq]; linarith)
  have hmem_p : p ∈ blumDyI m a := by
    rw [blumDyI]
    exact Set.mem_Ioo.mpr ⟨by rw [← hl]; exact hplr.1, by rw [← hr]; exact hplr.2⟩
  have hmem_q : q ∈ blumDyI m a := by
    rw [blumDyI]
    exact Set.mem_Ioo.mpr ⟨by rw [← hl]; exact hqlr.1, by rw [← hr]; exact hqlr.2⟩
  have hp' := (blumDyI_mem_iff m' a' p).mp (hsub hmem_p)
  have hq' := (blumDyI_mem_iff m' a' q).mp (hsub hmem_q)
  have hdist : (r - l) / 2 < 1 / 2 ^ m' := by
    have e : q - p = (r - l) / 2 := by rw [hp, hq]; ring
    have h1 : q * 2 ^ m' < (a' : ℝ) + 1 := hq'.2
    have h2 : (a' : ℝ) < p * 2 ^ m' := hp'.1
    have h3 : (q - p) * 2 ^ m' < 1 := by linarith [h1, h2]
    have h4 : (q - p) < 1 / 2 ^ m' := by
      rw [lt_div_iff₀ h2m']
      linarith [h3]
    rw [e] at h4
    exact h4
  have h2mne : (2 : ℝ) ^ m ≠ 0 := ne_of_gt h2m
  have hlen2 : (r - l) / 2 = 1 / 2 ^ (m + 1) := by
    rw [hlen, pow_succ]
    field_simp
  rw [hlen2] at hdist
  have hpow : (2 : ℝ) ^ m' < (2 : ℝ) ^ (m + 1) := by
    have h := (one_div_lt_one_div (by positivity : (0:ℝ) < 2 ^ (m+1))
      h2m').mp hdist
    exact h
  have hlt2 : m' < m + 1 :=
    (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hpow
  omega

-- N5f: every open neighborhood contains arbitrarily fine nonempty dyadic intervals.
theorem blum_dyI_small_mem_open {U : Set ℝ} (hUo : IsOpen U) {y : ℝ}
    (hy : y ∈ U) (M : ℕ) : ∃ m : ℕ, M ≤ m ∧ ∃ a : ℤ,
      blumDyI m a ⊆ U ∧ (blumDyI m a).Nonempty := by
  obtain ⟨r, hrpos, hrsub⟩ := Metric.isOpen_iff.mp hUo y hy
  have htend : Filter.Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) Filter.atTop
      (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hev : ∀ᶠ n : ℕ in Filter.atTop, ((1 : ℝ) / 2) ^ n < r / 2 :=
    htend.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < r / 2))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  set m := max N M with hm
  have hmM : M ≤ m := le_max_right _ _
  have hpow : ((1 : ℝ) / 2) ^ m < r / 2 := hN m (le_max_left _ _)
  have h12 : ((1 : ℝ) / 2) ^ m = 1 / (2 : ℝ) ^ m := by rw [div_pow, one_pow]
  rw [h12] at hpow
  have hballpos : (0 : ℝ) < 1 / 2 ^ m := by positivity
  have hdense := Set.Countable.dense_compl ℝ blum_dyadic_countable
  have hballne : (Metric.ball y (1 / 2 ^ m)).Nonempty :=
    (Metric.nonempty_ball (x := y)).mpr hballpos
  have hmeet := (dense_iff_inter_open.mp hdense) (Metric.ball y (1 / 2 ^ m))
    Metric.isOpen_ball hballne
  obtain ⟨z, hzball, hznd⟩ := hmeet
  have hzball' : dist z y < 1 / 2 ^ m := Metric.mem_ball.mp hzball
  have hznd' : z ∉ blumDyadic := hznd
  refine ⟨m, hmM, ⌊z * 2 ^ m⌋, ?_, ⟨z, blum_mem_dyI_floor m hznd'⟩⟩
  have hza := blum_mem_dyI_floor (m := m) hznd'
  intro w hw
  apply hrsub
  have hwz : w ∈ Metric.ball z (1 / 2 ^ m) :=
    blum_dyI_subset_ball m _ hza hw
  rw [Metric.mem_ball] at hwz ⊢
  have htri : dist w y ≤ dist w z + dist z y := dist_triangle _ _ _
  have hcomm : dist z y = dist y z := dist_comm _ _
  linarith [htri, hwz, hzball', hpow]

end MetaMathlibExt
end
