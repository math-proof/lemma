-- Author: @toskua, Avocado
-- Original KKM formalization by Adam Kiezun (`@akiezun`) in commit
-- `d855ffa90ad200e1ae118101768bd192d0d3c59f`; `@toskua, Avocado` authored
-- only the `Convexity.StdSimplex` representation migration.
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Def.Analysis.Convex.KKM.Part4
/-!
# Knaster-Kuratowski-Mazurkiewicz lemma

Proved via Sperner's lemma on iterated barycentric subdivisions plus a
mesh-shrinking limit argument: fully labeled simplices at every level, a
convergent subsequence in the compact simplex (mesh `(n/(n+1))^k → 0`), and
closedness of the cover. Vertices at level `k+1` are finsets of level-`k`
vertices; validity means a nonempty chain with supports in the coordinate
set; `BdPt` is barycentric realization in `Convexity.StdSimplex`.

Primary source: B. Knaster, C. Kuratowski, S. Mazurkiewicz,
"Ein Beweis des Fixpunktsatzes für n-dimensionale Simplexe",
Fundamenta Mathematicae 14 (1929), 132–137, DOI 10.4064/fm-14-1-132-137.
-/


namespace Convex.KKM

variable {n : ℕ}

/-- The Sperner label lies in the support. -/
lemma BdLabel_mem_supp {k : ℕ}
    {F : Fin (n + 1) → Set (Convexity.StdSimplex ℝ (Fin (n + 1)))}
    {hF_cover : ∀ x : Convexity.StdSimplex ℝ (Fin (n + 1)),
      ∃ i : Fin (n + 1), 0 < x.weights i ∧ x ∈ F i}
    {S : Finset (Fin (n + 1))} {v : BdV (n := n) k}
    (hv : BdValid S k {v}) : BdLabel F hF_cover S v ∈ BdSupp k v := by
  simp only [BdLabel, dite_eq_left hv]
  exact (Classical.choose_spec (BdLabel_exists F hF_cover v hv)).1

/-- The Sperner label's closed set contains the vertex point. -/
lemma BdLabel_mem_cover {k : ℕ}
    {F : Fin (n + 1) → Set (Convexity.StdSimplex ℝ (Fin (n + 1)))}
    {hF_cover : ∀ x : Convexity.StdSimplex ℝ (Fin (n + 1)),
      ∃ i : Fin (n + 1), 0 < x.weights i ∧ x ∈ F i}
    {S : Finset (Fin (n + 1))} {v : BdV (n := n) k}
    (hv : BdValid S k {v}) :
    BdSimp hv ∈ F (BdLabel F hF_cover S v) := by
  simp only [BdLabel, dite_eq_left hv]
  exact (Classical.choose_spec (BdLabel_exists F hF_cover v hv)).2

/-- Single-simplex parity, onto case: exactly one omitted-vertex facet has
label-set `t.erase c`. -/
lemma single_parity_surj {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (c : β) (hc : c ∈ t) (l : α → β)
    (hmaps : ∀ v ∈ s, l v ∈ t) (hm : s.card = t.card)
    (him : s.image l = t) :
    (s.filter (fun v => (s.erase v).image l = t.erase c)).card % 2 = 1 := by
  have hFib1 : ∀ y ∈ t, (s.filter (fun v => l v = y)).card ≥ 1 := by
    intro y hy
    have hy' : y ∈ s.image l := by rw [him]; exact hy
    obtain ⟨v, hvs, hvy⟩ := Finset.mem_image.mp hy'
    exact Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨hvs, hvy⟩⟩
  have hpart : ∑ y ∈ t, (s.filter (fun v => l v = y)).card = t.card := by
    have hunion : s = t.biUnion (fun y => s.filter (fun v => l v = y)) := by
      ext v
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · intro hvs
        exact ⟨l v, hmaps v hvs, hvs, rfl⟩
      · intro h
        obtain ⟨y, hy, hvs, hvy⟩ := h
        exact hvs
    have hdisj : Set.PairwiseDisjoint (↑t)
        (fun y => s.filter (fun v => l v = y)) := by
      intro y1 _ y2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      rw [Finset.mem_filter] at hv1 hv2
      exact hne (hv1.2.symm.trans hv2.2)
    calc ∑ y ∈ t, (s.filter (fun v => l v = y)).card
        = (t.biUnion (fun y => s.filter (fun v => l v = y))).card :=
          (Finset.card_biUnion hdisj).symm
      _ = s.card := by rw [← hunion]
      _ = t.card := hm
  have hsingle : ∀ y ∈ t, (s.filter (fun v => l v = y)).card = 1 := by
    have hsum0 : ∑ y ∈ t, ((s.filter (fun v => l v = y)).card - 1) = 0 := by
      rw [Finset.sum_tsub_distrib _ (fun y hy => hFib1 y hy), hpart]
      simp
    have hall0 : ∀ z ∈ t, (s.filter (fun v => l v = z)).card - 1 = 0 := by
      intro z hz
      have hiff := Finset.sum_eq_zero_iff_of_nonneg
        (s := t) (f := fun y => (s.filter (fun v => l v = y)).card - 1)
        (fun _ _ => Nat.zero_le _)
      exact (hiff.mp hsum0) z hz
    intro y hy
    have h1 := hFib1 y hy
    have h0 := hall0 y hy
    omega
  obtain ⟨v0, hv0⟩ := Finset.card_eq_one.mp (hsingle c hc)
  have hG : s.filter (fun v => (s.erase v).image l = t.erase c) = {v0} := by
    ext v
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro h
      obtain ⟨hvs, hgood⟩ := h
      have hcimg : c ∈ s.image l := by rw [him]; exact hc
      obtain ⟨w, hws, hw⟩ := Finset.mem_image.mp hcimg
      have hwfib : w ∈ s.filter (fun v => l v = c) :=
        Finset.mem_filter.mpr ⟨hws, hw⟩
      rw [hv0, Finset.mem_singleton] at hwfib
      by_contra hcon
      have hwne : w ≠ v := by
        rw [hwfib]
        exact fun h => hcon h.symm
      have hwerase : w ∈ s.erase v := Finset.mem_erase.mpr ⟨hwne, hws⟩
      have hcmem : c ∈ (s.erase v).image l :=
        Finset.mem_image.mpr ⟨w, hwerase, hw⟩
      rw [hgood] at hcmem
      exact Finset.notMem_erase c t hcmem
    · intro h
      subst v
      have hv0fib : v0 ∈ s.filter (fun v => l v = c) := by
        rw [hv0]
        exact Finset.mem_singleton_self v0
      rw [Finset.mem_filter] at hv0fib
      refine ⟨hv0fib.1, ?_⟩
      have hsub : (s.erase v0).image l ⊆ t.erase c := by
        intro y hy
        obtain ⟨w, hwerase, hwl⟩ := Finset.mem_image.mp hy
        rw [Finset.mem_erase] at hwerase
        rw [Finset.mem_erase]
        constructor
        · intro hcon
          have hlc : l w = c := hwl.trans hcon
          have hwfib : w ∈ s.filter (fun v => l v = c) :=
            Finset.mem_filter.mpr ⟨hwerase.2, hlc⟩
          rw [hv0, Finset.mem_singleton] at hwfib
          exact hwerase.1 hwfib
        · rw [← hwl]
          exact hmaps w hwerase.2
      have hcard : ((s.erase v0).image l).card = (t.erase c).card := by
        have hinj : Set.InjOn l ↑(s.erase v0) := by
          intro w1 hw1 w2 hw2 heq
          rw [Finset.mem_coe, Finset.mem_erase] at hw1 hw2
          have h1 : w1 ∈ s.filter (fun v => l v = l w1) :=
            Finset.mem_filter.mpr ⟨hw1.2, rfl⟩
          have h2 : w2 ∈ s.filter (fun v => l v = l w1) :=
            Finset.mem_filter.mpr ⟨hw2.2, heq.symm⟩
          have hsing := hsingle (l w1) (hmaps w1 hw1.2)
          obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hsing
          rw [hu, Finset.mem_singleton] at h1 h2
          exact h1.trans h2.symm
        rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem hv0fib.1,
          Finset.card_erase_of_mem hc, hm]
      exact Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
  rw [hG, Finset.card_singleton]

/-- Single-simplex parity, small-image case: no good facets. -/
lemma single_parity_small {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (c : β) (hc : c ∈ t) (l : α → β)
    (hlt : (s.image l).card + 1 < t.card) :
    (s.filter (fun v => (s.erase v).image l = t.erase c)).card % 2 = 0 := by
  have hGempty : s.filter (fun v => (s.erase v).image l = t.erase c) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro v hv
    rw [Finset.mem_filter] at hv
    obtain ⟨hvs, hgood⟩ := hv
    have hsub : (s.erase v).image l ⊆ s.image l := by
      intro y hy
      obtain ⟨w, hwerase, hwl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_image.mpr ⟨w, Finset.erase_subset v s hwerase, hwl⟩
    rw [hgood] at hsub
    have hle := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hc] at hle
    have htpos : 1 ≤ t.card := Finset.card_pos.mpr ⟨c, hc⟩
    omega
  rw [hGempty, Finset.card_empty]

/-- Single-simplex parity, wrong-missing-label case: no good facets. -/
lemma single_parity_wrong {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (c : β) (l : α → β)
    (d : β) (hd : d ∈ t) (hdc : d ≠ c) (hTd : s.image l = t.erase d) :
    (s.filter (fun v => (s.erase v).image l = t.erase c)).card % 2 = 0 := by
  have hGempty : s.filter (fun v => (s.erase v).image l = t.erase c) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro v hv
    rw [Finset.mem_filter] at hv
    obtain ⟨hvs, hgood⟩ := hv
    have hsub : (s.erase v).image l ⊆ t.erase d := by
      rw [← hTd]
      intro y hy
      obtain ⟨w, hwerase, hwl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_image.mpr ⟨w, Finset.erase_subset v s hwerase, hwl⟩
    rw [hgood] at hsub
    have hdmem : d ∈ t.erase c := Finset.mem_erase.mpr ⟨hdc, hd⟩
    have hcon := hsub hdmem
    exact Finset.notMem_erase d t hcon
  rw [hGempty, Finset.card_empty]

/-- Single-simplex parity, doubled-fiber case: exactly two good facets. -/
lemma single_parity_doubled {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (c : β) (hc : c ∈ t) (l : α → β)
    (_hmaps : ∀ v ∈ s, l v ∈ t) (hm : s.card = t.card)
    (hTd : s.image l = t.erase c) :
    (s.filter (fun v => (s.erase v).image l = t.erase c)).card % 2 = 0 := by
  have hFib1 : ∀ y ∈ t.erase c, (s.filter (fun v => l v = y)).card ≥ 1 := by
    intro y hy
    have hy' : y ∈ s.image l := by rw [hTd]; exact hy
    obtain ⟨v, hvs, hvy⟩ := Finset.mem_image.mp hy'
    exact Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨hvs, hvy⟩⟩
  have hpart : ∑ y ∈ t.erase c, (s.filter (fun v => l v = y)).card = s.card := by
    have hunion : s = (t.erase c).biUnion
        (fun y => s.filter (fun v => l v = y)) := by
      ext v
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · intro hvs
        have hmem : l v ∈ t.erase c := by
          have himg : l v ∈ s.image l :=
            Finset.mem_image.mpr ⟨v, hvs, rfl⟩
          rw [hTd] at himg
          exact himg
        exact ⟨l v, hmem, hvs, rfl⟩
      · intro h
        obtain ⟨y, hy, hvs, hvy⟩ := h
        exact hvs
    have hdisj : Set.PairwiseDisjoint (↑(t.erase c))
        (fun y => s.filter (fun v => l v = y)) := by
      intro y1 _ y2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      rw [Finset.mem_filter] at hv1 hv2
      exact hne (hv1.2.symm.trans hv2.2)
    calc ∑ y ∈ t.erase c, (s.filter (fun v => l v = y)).card
        = ((t.erase c).biUnion (fun y => s.filter (fun v => l v = y))).card :=
          (Finset.card_biUnion hdisj).symm
      _ = s.card := by rw [← hunion]
  have hspos : 1 ≤ s.card := by
    rw [hm]
    exact Finset.card_pos.mpr ⟨c, hc⟩
  have hcardT : (t.erase c).card = s.card - 1 := by
    rw [Finset.card_erase_of_mem hc, ← hm]
  have hsum1 : ∑ y ∈ t.erase c, ((s.filter (fun v => l v = y)).card - 1) = 1 := by
    rw [Finset.sum_tsub_distrib _ (fun y hy => hFib1 y hy), hpart]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_id]
    rw [hcardT]
    omega
  obtain ⟨tstar, htstar, hstar1, hstar0⟩ :
      ∃ tstar ∈ t.erase c, (s.filter (fun v => l v = tstar)).card = 2 ∧
        ∀ y ∈ t.erase c, y ≠ tstar →
          (s.filter (fun v => l v = y)).card = 1 := by
    have hex : ∃ tstar ∈ t.erase c,
        (s.filter (fun v => l v = tstar)).card - 1 ≠ 0 := by
      by_contra hcon
      have hall : ∀ tstar ∈ t.erase c,
          (s.filter (fun v => l v = tstar)).card - 1 = 0 := by
        intro tstar htstar
        by_contra hne2
        exact hcon ⟨tstar, htstar, hne2⟩
      have h0 := Finset.sum_eq_zero hall
      omega
    obtain ⟨tstar, htstar, hgne⟩ := hex
    have hub : ∀ y ∈ t.erase c,
        (s.filter (fun v => l v = y)).card - 1 ≠ 0 → y = tstar := by
      intro y hy hgy
      by_contra hne
      have hle : (s.filter (fun v => l v = tstar)).card - 1 +
          ((s.filter (fun v => l v = y)).card - 1) ≤
          ∑ z ∈ t.erase c, ((s.filter (fun v => l v = z)).card - 1) := by
        have hsub : ({tstar, y} : Finset β) ⊆ t.erase c := by
          intro z hz
          rw [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact htstar
          · exact hy
        have hle2 := Finset.sum_le_sum_of_subset_of_nonneg
          (s := ({tstar, y} : Finset β)) (t := t.erase c)
          (f := fun z => (s.filter (fun v => l v = z)).card - 1)
          hsub (fun _ _ _ => Nat.zero_le _)
        rw [Finset.sum_pair (fun h => hne h.symm)] at hle2
        exact hle2
      have g1 : 1 ≤ (s.filter (fun v => l v = tstar)).card - 1 :=
        Nat.pos_of_ne_zero hgne
      have g2 : 1 ≤ (s.filter (fun v => l v = y)).card - 1 :=
        Nat.pos_of_ne_zero hgy
      omega
    have h1 : (s.filter (fun v => l v = tstar)).card - 1 = 1 := by
      have hsingle0 := Finset.sum_eq_single tstar
        (s := t.erase c) (f := fun y => (s.filter (fun v => l v = y)).card - 1)
        (fun y hy hne => by
          by_contra hgy
          exact hne (hub y hy hgy))
        (fun h => absurd htstar h)
      omega
    refine ⟨tstar, htstar, ?_, ?_⟩
    · have hfi := hFib1 tstar htstar
      omega
    · intro y hy hne
      by_contra hcon
      have hgy : (s.filter (fun v => l v = y)).card - 1 ≠ 0 := by
        have hfi := hFib1 y hy
        omega
      exact hne (hub y hy hgy)
  have hGchar : ∀ v ∈ s, ((s.erase v).image l = t.erase c ↔
      2 ≤ (s.filter (fun w => l w = l v)).card) := by
    intro v hvs
    constructor
    · intro hgood
      have hmem : l v ∈ t.erase c := by
        have himg : l v ∈ s.image l :=
          Finset.mem_image.mpr ⟨v, hvs, rfl⟩
        rw [hTd] at himg
        exact himg
      rw [← hgood] at hmem
      obtain ⟨w, hwerase, hwl⟩ := Finset.mem_image.mp hmem
      rw [Finset.mem_erase] at hwerase
      have hsub : ({v, w} : Finset α) ⊆ s.filter (fun u => l u = l v) := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨hvs, rfl⟩
        · exact Finset.mem_filter.mpr ⟨hwerase.2, hwl⟩
      have hle := Finset.card_le_card hsub
      rw [Finset.card_pair hwerase.1.symm] at hle
      exact hle
    · intro h2
      have hsub1 : (s.erase v).image l ⊆ t.erase c := by
        intro y hy
        obtain ⟨w, hwerase, hwl⟩ := Finset.mem_image.mp hy
        rw [Finset.mem_erase]
        constructor
        · intro hcon
          have himg : l w ∈ s.image l := Finset.mem_image.mpr
            ⟨w, Finset.erase_subset v s hwerase, rfl⟩
          rw [hTd, Finset.mem_erase] at himg
          exact himg.1 (hwl.trans hcon)
        · have himg : l w ∈ s.image l := Finset.mem_image.mpr
            ⟨w, Finset.erase_subset v s hwerase, rfl⟩
          rw [hTd, Finset.mem_erase] at himg
          rw [← hwl]
          exact himg.2
      have hsub2 : t.erase c ⊆ (s.erase v).image l := by
        intro y hy
        rw [Finset.mem_erase] at hy
        obtain ⟨hync, hyt⟩ := hy
        have hyimg : y ∈ s.image l := by
          rw [hTd]
          exact Finset.mem_erase.mpr ⟨hync, hyt⟩
        obtain ⟨u, hus, huy⟩ := Finset.mem_image.mp hyimg
        by_cases huv : u = v
        · subst u
          have hmemv : v ∈ s.filter (fun w => l w = l v) :=
            Finset.mem_filter.mpr ⟨hvs, rfl⟩
          have hss : ({v} : Finset α) ⊂ s.filter (fun w => l w = l v) := by
            refine ⟨?_, ?_⟩
            · intro x hx
              rw [Finset.mem_singleton] at hx
              obtain rfl := hx
              exact hmemv
            · intro hcon
              have hle := Finset.card_le_card hcon
              rw [Finset.card_singleton] at hle
              omega
          obtain ⟨w, hwfib, hwnsing⟩ := Finset.exists_of_ssubset hss
          rw [Finset.mem_filter] at hwfib
          rw [Finset.mem_singleton] at hwnsing
          have hwerase : w ∈ s.erase v :=
            Finset.mem_erase.mpr ⟨hwnsing, hwfib.1⟩
          have huy2 : l w = y := hwfib.2.trans huy
          exact Finset.mem_image.mpr ⟨w, hwerase, huy2⟩
        · have huerase : u ∈ s.erase v := Finset.mem_erase.mpr ⟨huv, hus⟩
          exact Finset.mem_image.mpr ⟨u, huerase, huy⟩
      exact Finset.Subset.antisymm hsub1 hsub2
  have hGeq : s.filter (fun v => (s.erase v).image l = t.erase c) =
      s.filter (fun v => l v = tstar) := by
    ext v
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · intro h
      obtain ⟨hvs, hgood⟩ := h
      have h2 := (hGchar v hvs).mp hgood
      have hmem : l v ∈ t.erase c := by
        have himg : l v ∈ s.image l :=
          Finset.mem_image.mpr ⟨v, hvs, rfl⟩
        rw [hTd] at himg
        exact himg
      have heq : l v = tstar := by
        by_contra hne
        have h1 := hstar0 (l v) hmem hne
        omega
      exact ⟨hvs, heq⟩
    · intro h
      obtain ⟨hvs, hlv⟩ := h
      refine ⟨hvs, ?_⟩
      have h2 : 2 ≤ (s.filter (fun w => l w = l v)).card := by
        rw [hlv]
        omega
      exact (hGchar v hvs).mpr h2
  rw [hGeq, hstar1]

/-- Single-simplex Sperner parity: the number of omitted-vertex facets with
label-set `t.erase c` is odd iff the labeling is onto `t`. -/
lemma single_parity {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (c : β) (hc : c ∈ t) (l : α → β)
    (hmaps : ∀ v ∈ s, l v ∈ t) (hm : s.card = t.card) :
    (s.filter (fun v => (s.erase v).image l = t.erase c)).card % 2 =
      (if s.image l = t then 1 else 0) := by
  by_cases him : s.image l = t
  · rw [ite_eq_left him]
    exact single_parity_surj s t c hc l hmaps hm him
  · rw [ite_eq_right him]
    have himgsub : s.image l ⊆ t := by
      intro y hy
      obtain ⟨v, hvs, hvy⟩ := Finset.mem_image.mp hy
      rw [← hvy]
      exact hmaps v hvs
    have hcardlt : (s.image l).card < t.card :=
      Finset.card_lt_card ⟨himgsub, fun h => him (Finset.Subset.antisymm himgsub h)⟩
    by_cases hcard : (s.image l).card + 1 = t.card
    · obtain ⟨d, hd, hTd⟩ : ∃ d ∈ t, s.image l = t.erase d := by
        have hcompl : (t \ s.image l).card = 1 := by
          have hinter : s.image l ∩ t = s.image l := by
            ext y
            simp only [Finset.mem_inter]
            constructor
            · exact And.left
            · intro hy
              exact ⟨hy, himgsub hy⟩
          rw [Finset.card_sdiff, hinter]
          omega
        obtain ⟨d, hdeq⟩ := Finset.card_eq_one.mp hcompl
        have hdmem : d ∈ t := by
          have hmem : d ∈ t \ s.image l := by
            rw [hdeq]
            exact Finset.mem_singleton_self d
          exact (Finset.mem_sdiff.mp hmem).1
        refine ⟨d, hdmem, ?_⟩
        ext y
        constructor
        · intro hy
          rw [Finset.mem_erase]
          refine ⟨?_, himgsub hy⟩
          intro hcon
          subst y
          have hdT : d ∈ t \ s.image l := by
            rw [hdeq]
            exact Finset.mem_singleton_self d
          exact (Finset.mem_sdiff.mp hdT).2 hy
        · intro hy
          rw [Finset.mem_erase] at hy
          by_contra hcon
          have hmem : y ∈ t \ s.image l := Finset.mem_sdiff.mpr ⟨hy.2, hcon⟩
          rw [hdeq, Finset.mem_singleton] at hmem
          exact hy.1 hmem
      by_cases hdc : d = c
      · subst d
        exact single_parity_doubled s t c hc l hmaps hm hTd
      · exact single_parity_wrong s t c l d hd hdc hTd
    · have hlt : (s.image l).card + 1 < t.card := by omega
      exact single_parity_small s t c hc l hlt

end Convex.KKM
