import sympy.concrete.quantifier
import sympy.series.limits
import sympy.sets.sets
import sympy.Basic


@[main, comm, mp, mpr]
private lemma εδ
-- given
  (f : ℝ → ℝ)
  (x₀ a : ℝ) :
-- imply
  lim [x → x₀] f x = a ↔ ∀ ε > 0, ∃ δ > 0, ∀ x | |x - x₀| ∈ Ioo 0 δ, |f x - a| < ε := by
-- proof
  constructor
  ·
    intro h ε hε
    obtain ⟨δ, hδ, H⟩ := Metric.tendsto_nhdsWithin_nhds.mp h ε hε
    refine ⟨δ, hδ, fun x hx => ?_⟩
    simpa [Real.dist_eq] using H (Set.mem_compl_singleton_iff.mpr (sub_ne_zero.mp (abs_pos.mp hx.1))) (by simpa [Real.dist_eq] using hx.2)
  ·
    intro h
    apply Metric.tendsto_nhdsWithin_nhds.mpr
    intro ε hε
    obtain ⟨δ, hδ, H⟩ := h ε hε
    refine ⟨δ, hδ, fun x hx hxδ => ?_⟩
    simpa [Real.dist_eq] using H x ⟨abs_pos.mpr (sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hx)), by simpa [Real.dist_eq] using hxδ⟩


@[main, comm, mp, mpr]
private lemma εδ.pos
-- given
  (f : ℝ → ℝ)
  (x₀ a : ℝ) :
-- imply
  lim [x → x₀⁺] f x = a ↔ ∀ ε > 0, ∃ δ > 0, ∀ x | x - x₀ ∈ Ioo 0 δ, |f x - a| < ε := by
-- proof
  constructor
  ·
    intro h ε hε
    obtain ⟨δ, hδ, H⟩ := Metric.tendsto_nhdsWithin_nhds.mp h ε hε
    refine ⟨δ, hδ, fun x hx => ?_⟩
    simpa [Real.dist_eq, abs_of_pos hx.1] using H (Set.mem_Ioi.mpr (sub_pos.mp hx.1)) (by simpa [Real.dist_eq, abs_of_pos hx.1] using hx.2)
  ·
    intro h
    apply Metric.tendsto_nhdsWithin_nhds.mpr
    intro ε hε
    obtain ⟨δ, hδ, H⟩ := h ε hε
    refine ⟨δ, hδ, fun x hx hxδ => ?_⟩
    have hx' := sub_pos.mpr (Set.mem_Ioi.mp hx)
    simpa [Real.dist_eq] using H x ⟨hx', by simpa [Real.dist_eq, abs_of_pos hx'] using hxδ⟩


@[main, comm, mp, mpr]
private lemma εδ.neg
-- given
  (f : ℝ → ℝ)
  (x₀ a : ℝ) :
-- imply
  lim [x → x₀⁻] f x = a ↔ ∀ ε > 0, ∃ δ > 0, ∀ x | x₀ - x ∈ Ioo 0 δ, |f x - a| < ε := by
-- proof
  constructor
  ·
    intro h ε hε
    obtain ⟨δ, hδ, H⟩ := Metric.tendsto_nhdsWithin_nhds.mp h ε hε
    refine ⟨δ, hδ, fun x hx => ?_⟩
    have hxlt := sub_pos.mp hx.1
    simpa [Real.dist_eq, abs_of_neg (sub_neg.mpr hxlt)] using H (Set.mem_Iio.mpr hxlt) (by simpa [Real.dist_eq, abs_of_neg (sub_neg.mpr hxlt)] using hx.2)
  ·
    intro h
    apply Metric.tendsto_nhdsWithin_nhds.mpr
    intro ε hε
    obtain ⟨δ, hδ, H⟩ := h ε hε
    refine ⟨δ, hδ, fun x hx hxδ => ?_⟩
    have hxlt := Set.mem_Iio.mp hx
    have hx' := sub_pos.mpr hxlt
    simpa [Real.dist_eq] using H x ⟨hx', by simpa [Real.dist_eq, abs_of_neg (sub_neg.mpr hxlt)] using hxδ⟩


@[main, comm, mp, mpr]
private lemma εN.pos
  [LinearOrder α]
  [Zero α]
  [One α]
  [NoMaxOrder α]
  [ZeroLEOneClass α]
  [NeZero (1 : α)]
-- given
  (f : α → ℝ)
  (a : ℝ) :
-- imply
  lim [x → ∞] f x = a ↔ ∀ ε > 0, ∃ N > 0, ∀ x | x > N, |f x - a| < ε := by
-- proof
  constructor
  ·
    intro h ε hε
    obtain ⟨N, H⟩ := Metric.tendsto_atTop'.mp h ε hε
    refine ⟨max N 1, lt_max_of_lt_right zero_lt_one, fun x hx => ?_⟩
    simpa [Real.dist_eq] using H x (lt_of_le_of_lt (le_max_left N 1) hx)
  ·
    intro h
    apply Metric.tendsto_atTop'.mpr
    intro ε hε
    obtain ⟨N, _, H⟩ := h ε hε
    refine ⟨N, fun x hx => ?_⟩
    simpa [Real.dist_eq] using H x hx


@[main, comm, mp, mpr]
private lemma εN.neg
  [AddCommGroup α]
  [LinearOrder α]
  [IsOrderedAddMonoid α]
  [One α]
  [ZeroLEOneClass α]
  [NeZero (1 : α)]
-- given
  (f : α → ℝ)
  (a : ℝ) :
-- imply
  lim [x → -∞] f x = a ↔ ∀ ε > 0, ∃ N > 0, ∀ x | x < -N, |f x - a| < ε := by
-- proof
  constructor
  ·
    intro h ε hε
    obtain ⟨N, H⟩ := Filter.eventually_atBot.mp (Metric.tendsto_nhds.mp h ε hε)
    refine ⟨max (-N) 1, lt_max_of_lt_right zero_lt_one, fun x hx => ?_⟩
    have hxN : x ≤ N :=
      le_trans (le_of_lt hx)
        ((neg_le_neg (le_max_left (-N) 1)).trans_eq (neg_neg N))
    simpa [Real.dist_eq] using H x hxN
  ·
    intro h
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨N, _, H⟩ := h ε hε
    refine Filter.eventually_atBot.mpr ⟨-N - 1, fun x hx => ?_⟩
    simpa [Real.dist_eq] using H x (lt_of_le_of_lt hx (sub_lt_self _ zero_lt_one))


-- created on 2020-04-03
-- updated on 2026-08-20
