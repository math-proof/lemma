/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Algebra.Group.End
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.Chain
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Road coloring theorem

This file proves the road coloring theorem of A. N. Trahtman, "The road coloring problem",
Israel J. Math. 172 (2009) 51–60. The proof follows the reduction of Culik, Karhumäki and Kari:
a recoloring with a stable pair passes to a smaller quotient automaton, and synchronizing words
lift back. Stable pairs come from two bunches into one vertex, or else from Trahtman's lemma on
spanning subgraphs with a unique highest tree, via Kari's minimal-rank argument.
-/

namespace MetaMathlibExt

section

namespace RoadColoring

private def rc_adj {V : Type*} {k : ℕ} (delta : V → Fin k → V) (v w : V) : Prop :=
  ∃ a : Fin k, delta v a = w

private def rc_recolor {V : Type*} {k : ℕ} (delta : V → Fin k → V)
    (sigma : V → Equiv.Perm (Fin k)) : V → Fin k → V :=
  fun v a => delta v (sigma v a)

private def rc_sync {V : Type*} {k : ℕ} (delta : V → Fin k → V) : Prop :=
  ∃ (word : List (Fin k)) (r : V), ∀ v : V, List.foldl delta v word = r

private def rc_strongly {V : Type*} {k : ℕ} (delta : V → Fin k → V) : Prop :=
  ∀ u v : V, Relation.ReflTransGen (rc_adj delta) u v

private def rc_aperiodic {V : Type*} {k : ℕ} (delta : V → Fin k → V) : Prop :=
  ∀ d : ℕ, 1 < d → ∃ (u : V) (w : List V),
    List.IsChain (rc_adj delta) (u :: w) ∧ w.getLast? = some u ∧ ¬ (d ∣ w.length)

private def rc_stable {V : Type*} {k : ℕ} (delta : V → Fin k → V) (p q : V) : Prop :=
  ∀ u : List (Fin k), ∃ v : List (Fin k),
    List.foldl delta p (u ++ v) = List.foldl delta q (u ++ v)

private theorem rc_stable_refl {V : Type*} {k : ℕ} (delta : V → Fin k → V) (p : V) :
    rc_stable delta p p := fun u => ⟨[], by simp⟩

private theorem rc_stable_symm {V : Type*} {k : ℕ} (delta : V → Fin k → V)
    {p q : V} (h : rc_stable delta p q) : rc_stable delta q p :=
  fun u => by obtain ⟨v, hv⟩ := h u; exact ⟨v, hv.symm⟩

private theorem rc_stable_trans {V : Type*} {k : ℕ} (delta : V → Fin k → V)
    {p q s : V} (hpq : rc_stable delta p q) (hqs : rc_stable delta q s) :
    rc_stable delta p s := by
  intro u
  obtain ⟨v1, hv1⟩ := hpq u
  obtain ⟨v2, hv2⟩ := hqs (u ++ v1)
  refine ⟨v1 ++ v2, ?_⟩
  have assoc : (u ++ v1) ++ v2 = u ++ (v1 ++ v2) := List.append_assoc u v1 v2
  have ep : List.foldl delta p (u ++ (v1 ++ v2)) =
      List.foldl delta (List.foldl delta p (u ++ v1)) v2 := by
    rw [← assoc, List.foldl_append]
  have es : List.foldl delta s (u ++ (v1 ++ v2)) =
      List.foldl delta (List.foldl delta s (u ++ v1)) v2 := by
    rw [← assoc, List.foldl_append]
  have qe : List.foldl delta q ((u ++ v1) ++ v2) =
      List.foldl delta (List.foldl delta q (u ++ v1)) v2 :=
    List.foldl_append
  have se : List.foldl delta s ((u ++ v1) ++ v2) =
      List.foldl delta (List.foldl delta s (u ++ v1)) v2 :=
    List.foldl_append
  have hv2' : List.foldl delta (List.foldl delta q (u ++ v1)) v2 =
      List.foldl delta (List.foldl delta s (u ++ v1)) v2 := by
    rw [← qe, ← se]
    exact hv2
  calc List.foldl delta p (u ++ (v1 ++ v2))
      = List.foldl delta (List.foldl delta p (u ++ v1)) v2 := ep
    _ = List.foldl delta (List.foldl delta q (u ++ v1)) v2 := by rw [hv1]
    _ = List.foldl delta (List.foldl delta s (u ++ v1)) v2 := hv2'
    _ = List.foldl delta s (u ++ (v1 ++ v2)) := es.symm

private theorem rc_stable_foldl {V : Type*} {k : ℕ} (delta : V → Fin k → V)
    {p q : V} (h : rc_stable delta p q) (w : List (Fin k)) :
    rc_stable delta (List.foldl delta p w) (List.foldl delta q w) := by
  intro u
  obtain ⟨v, hv⟩ := h (w ++ u)
  refine ⟨v, ?_⟩
  have assoc : (w ++ u) ++ v = w ++ (u ++ v) := List.append_assoc w u v
  have e1 : List.foldl delta p ((w ++ u) ++ v) =
      List.foldl delta (List.foldl delta p w) (u ++ v) := by
    rw [assoc, List.foldl_append, List.foldl_append]
  have e2 : List.foldl delta q ((w ++ u) ++ v) =
      List.foldl delta (List.foldl delta q w) (u ++ v) := by
    rw [assoc, List.foldl_append, List.foldl_append]
  rw [e1] at hv
  rw [e2] at hv
  exact hv

private theorem rc_exists_merge_of_pairwise_stable {V : Type*} [Nonempty V]
    {k : ℕ} (delta : V → Fin k → V) :
    ∀ S : Finset V, (∀ p ∈ S, ∀ q ∈ S, rc_stable delta p q) →
    ∃ w : List (Fin k), ∃ r : V, ∀ v ∈ S, List.foldl delta v w = r := by
  classical
  obtain ⟨r₀⟩ := (‹Nonempty V› : Nonempty V)
  have key : ∀ m : ℕ, ∀ T : Finset V, T.card ≤ m →
      (∀ p ∈ T, ∀ q ∈ T, rc_stable delta p q) →
      ∃ w : List (Fin k), ∃ r : V, ∀ v ∈ T, List.foldl delta v w = r := by
    intro m
    induction m with
    | zero =>
      intro T hcard h
      have hempty : T = ∅ := Finset.card_eq_zero.mp (by omega)
      exact ⟨[], r₀,
        fun v hv => by rw [hempty] at hv; exact absurd hv (Finset.notMem_empty v)⟩
    | succ m ih =>
      intro T hcard h
      by_cases hle : T.card ≤ 1
      · by_cases hT : T.Nonempty
        · obtain ⟨p, hp⟩ := hT
          refine ⟨[], p, fun v hv => ?_⟩
          have hvp : v = p := Finset.card_le_one_iff.mp hle hv hp
          rw [hvp]
          rfl
        · have hT' : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
          exact ⟨[], r₀,
            fun v hv => by rw [hT'] at hv; exact absurd hv (Finset.notMem_empty v)⟩
      · obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
        have hcardE : 0 < (T.erase p).card := by
          rw [Finset.card_erase_of_mem hp]
          omega
        obtain ⟨q, hq⟩ := Finset.card_pos.mp hcardE
        have hqT : q ∈ T := Finset.mem_of_mem_erase hq
        have hne : q ≠ p := Finset.ne_of_mem_erase hq
        obtain ⟨t, ht⟩ := rc_stable_merge delta (h p hp q hqT)
        have hlt : (T.image (fun x => List.foldl delta x t)).card < T.card := by
          by_contra hcon
          have hle2 := Finset.card_image_le (s := T)
            (f := fun x => List.foldl delta x t)
          have heq : (T.image (fun x => List.foldl delta x t)).card = T.card := by
            omega
          have hinj := Finset.card_image_iff.mp heq
          exact hne (hinj (Finset.mem_coe.mpr hp) (Finset.mem_coe.mpr hqT) ht).symm
        have hstab : ∀ y₁ ∈ T.image (fun x => List.foldl delta x t),
            ∀ y₂ ∈ T.image (fun x => List.foldl delta x t),
            rc_stable delta y₁ y₂ := by
          intro y₁ hy₁ y₂ hy₂
          obtain ⟨x₁, hx₁, rfl⟩ := Finset.mem_image.mp hy₁
          obtain ⟨x₂, hx₂, rfl⟩ := Finset.mem_image.mp hy₂
          exact rc_stable_foldl delta (h x₁ hx₁ x₂ hx₂) t
        obtain ⟨w', r, hr⟩ := ih _ (by omega) hstab
        exact ⟨t ++ w', r, fun v hv => by
          rw [List.foldl_append]
          exact hr _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)⟩
  intro S hS
  exact key S.card S le_rfl hS

private noncomputable def rc_minRank {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (delta : V → Fin k → V) : ℕ := by
  classical
  exact Nat.find (p := fun n => ∃ w : List (Fin k),
    (Finset.univ.image (fun v => List.foldl delta v w)).card = n)
    ⟨Fintype.card V, [], by simp⟩

private theorem rc_level_exists {V : Type*} [Finite V] (g : V → V) (v : V) :
    ∃ i : ℕ, g^[i] v ∈ Function.periodicPts g := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have hstep : ∀ a b : ℕ, g^[a] v = g^[b] v → a < b →
      g^[b - a] (g^[a] v) = g^[a] v := by
    intro a b heq hab
    have hd : b = a + (b - a) := by omega
    have e : g^[a + (b - a)] v = g^[b - a] (g^[a] v) := by
      rw [Nat.add_comm a (b - a)]
      exact Function.iterate_add_apply g (b - a) a v
    have hper : g^[b - a] (g^[a] v) = g^[a] v := by
      rw [← e, ← hd]
      exact heq.symm
    exact hper
  obtain ⟨x, y, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (Fintype.card V + 1) => g^[i.1] v) (by
      rw [Fintype.card_fin]
      omega)
  have hxy : x.1 ≠ y.1 := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · exact ⟨x.1, Function.mem_periodicPts.mpr
      ⟨y.1 - x.1, by omega, hstep x.1 y.1 heq hlt⟩⟩
  · exact ⟨y.1, Function.mem_periodicPts.mpr
      ⟨x.1 - y.1, by omega, hstep y.1 x.1 heq.symm hlt⟩⟩

private noncomputable def rc_level {V : Type*} [Finite V] (g : V → V) (v : V) : ℕ := by
  classical
  have : Fintype V := Fintype.ofFinite V
  exact Nat.find (p := fun i => g^[i] v ∈ Function.periodicPts g)
    (rc_level_exists g v)

private noncomputable def rc_root {V : Type*} [Finite V] (g : V → V) (v : V) : V :=
  g^[rc_level g v] v

private theorem rc_level_spec {V : Type*} [Finite V] (g : V → V) (v : V) :
    g^[rc_level g v] v ∈ Function.periodicPts g := by
  classical
  have : Fintype V := Fintype.ofFinite V
  unfold rc_level
  exact Nat.find_spec (p := fun i => g^[i] v ∈ Function.periodicPts g)
    (rc_level_exists g v)

private theorem rc_level_notMem {V : Type*} [Finite V] (g : V → V) (v : V)
    {m : ℕ} (hm : m < rc_level g v) : g^[m] v ∉ Function.periodicPts g := by
  classical
  have : Fintype V := Fintype.ofFinite V
  unfold rc_level at hm
  exact Nat.find_min (p := fun i => g^[i] v ∈ Function.periodicPts g)
    (rc_level_exists g v) hm

private theorem rc_level_le_of_mem {V : Type*} [Finite V] (g : V → V) (v : V)
    {i : ℕ} (hi : g^[i] v ∈ Function.periodicPts g) :
    rc_level g v ≤ i := by
  classical
  have : Fintype V := Fintype.ofFinite V
  unfold rc_level
  exact Nat.find_min' (p := fun i => g^[i] v ∈ Function.periodicPts g)
    (rc_level_exists g v) hi

private theorem rc_level_step {V : Type*} [Finite V] (g : V → V) (v : V)
    (hv : v ∉ Function.periodicPts g) :
    rc_level g (g v) = rc_level g v - 1 := by
  classical
  have hLpos : 0 < rc_level g v := by
    by_contra hcon
    have h0 : rc_level g v = 0 := by omega
    rw [rc_level_zero_iff] at h0
    exact hv h0
  have hL : 1 ≤ rc_level g v := hLpos
  have hdecomp : rc_level g v - 1 + 1 = rc_level g v := by omega
  have hmem : g^[rc_level g v - 1] (g v) ∈ Function.periodicPts g := by
    have hspec := rc_level_spec g v
    rw [← hdecomp, rc_iterate_succ_right] at hspec
    exact hspec
  have hle : rc_level g (g v) ≤ rc_level g v - 1 :=
    rc_level_le_of_mem g (g v) hmem
  have hge : rc_level g v - 1 ≤ rc_level g (g v) := by
    by_contra hcon
    have hlt : rc_level g (g v) < rc_level g v - 1 := by omega
    have hnot := rc_level_notMem g v
      (m := rc_level g (g v) + 1) (by omega)
    have heq : g^[rc_level g (g v) + 1] v =
        g^[rc_level g (g v)] (g v) := by
      rw [show rc_level g (g v) + 1 = rc_level g (g v) + 1 from rfl]
      exact (rc_iterate_succ_right g (rc_level g (g v)) v).symm
    rw [heq] at hnot
    exact hnot (rc_level_spec g (g v))
  omega

private theorem rc_root_step {V : Type*} [Finite V] (g : V → V) (v : V)
    (hv : v ∉ Function.periodicPts g) :
    rc_root g (g v) = rc_root g v := by
  classical
  have hLpos : 0 < rc_level g v := by
    by_contra hcon
    have h0 : rc_level g v = 0 := by omega
    rw [rc_level_zero_iff] at h0
    exact hv h0
  have hdecomp : rc_level g v - 1 + 1 = rc_level g v := by omega
  unfold rc_root
  rw [rc_level_step g v hv]
  have hspec : g^[rc_level g v - 1] (g v) = g^[rc_level g v] v := by
    conv_rhs => rw [← hdecomp]
    exact (rc_iterate_succ_right g _ v).symm
  exact hspec

private theorem rc_root_periodic {V : Type*} [Finite V] (g : V → V) (v : V) :
    rc_root g v ∈ Function.periodicPts g :=
  rc_level_spec g v

private theorem rc_level_root_zero {V : Type*} [Finite V] (g : V → V) (v : V) :
    rc_level g (rc_root g v) = 0 := by
  rw [rc_level_zero_iff]
  exact rc_root_periodic g v

private noncomputable def rc_height {V : Type*} [Fintype V] [DecidableEq V]
    (g : V → V) : ℕ :=
  Finset.sup Finset.univ (fun v => rc_level g v)

private noncomputable def rc_cyc {V : Type*} [Fintype V] [DecidableEq V]
    (g : V → V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun v => v ∈ Function.periodicPts g)).card

private def rc_good {V : Type*} [Fintype V] [DecidableEq V] (g : V → V) : Prop :=
  0 < rc_height g ∧ ∀ v w : V, rc_level g v = rc_height g →
    rc_level g w = rc_height g → rc_root g v = rc_root g w

private theorem rc_iterate_ge_level_periodic {V : Type*} [Finite V]
    (g : V → V) (v : V) {j : ℕ} (hj : rc_level g v ≤ j) :
    g^[j] v ∈ Function.periodicPts g := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [Nat.add_comm (rc_level g v) d, Function.iterate_add_apply]
  exact rc_periodic_iterate g (rc_level_spec g v) d

private theorem rc_iterate_height_periodic {V : Type*} [Fintype V] [DecidableEq V]
    (g : V → V) (v : V) : g^[rc_height g] v ∈ Function.periodicPts g :=
  rc_iterate_ge_level_periodic g v (rc_level_le_height g v)

private theorem rc_pred_notMem_of_top {V : Type*} [Fintype V] [DecidableEq V]
    (g : V → V) {p : V} (hp : rc_level g p = rc_height g)
    (hH : 1 ≤ rc_height g) : g^[rc_height g - 1] p ∉ Function.periodicPts g := by
  intro hmem
  have hle := rc_level_le_of_mem g p hmem
  omega

private theorem rc_level_eq_height_of_pred_notMem {V : Type*} [Fintype V]
    [DecidableEq V] (g : V → V) (L : ℕ) (hL : rc_height g = L)
    (v : V) (hv : g^[L - 1] v ∉ Function.periodicPts g) (hL1 : 1 ≤ L) :
    rc_level g v = L := by
  have hle : rc_level g v ≤ L := by rw [← hL]; exact rc_level_le_height g v
  by_contra hne
  have hlt : rc_level g v < L := by omega
  have hmem : g^[L - 1] v ∈ Function.periodicPts g := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show rc_level g v ≤ L - 1 by omega)
    have hspec := rc_level_spec g v
    have e : L - 1 = rc_level g v + d := hd
    rw [e, Nat.add_comm (rc_level g v) d, Function.iterate_add_apply]
    exact rc_periodic_iterate g hspec d
  exact hv hmem

private theorem rc_good_bridge {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (g : V → V) (hgood : rc_good g) :
    ∃ (L : ℕ) (r p : V), 1 ≤ L ∧ L = rc_height g ∧ rc_level g p = rc_height g ∧
      r = rc_root g p ∧ (∀ v, g^[L] v ∈ Function.periodicPts g) ∧
      g^[L - 1] p ∉ Function.periodicPts g ∧
      (∀ v, g^[L - 1] v ∉ Function.periodicPts g → g^[L] v = r) := by
  classical
  obtain ⟨hHpos, huniq⟩ := hgood
  obtain ⟨p, hp⟩ := rc_height_attained g
  have hH1 : 1 ≤ rc_height g := hHpos
  refine ⟨rc_height g, rc_root g p, p, hH1, rfl, hp, rfl, ?_, ?_, ?_⟩
  · intro v
    exact rc_iterate_height_periodic g v
  · exact rc_pred_notMem_of_top g hp hH1
  · intro v hv
    have hLv : rc_level g v = rc_height g :=
      rc_level_eq_height_of_pred_notMem g (rc_height g) rfl v hv hH1
    have e1 : g^[rc_height g] v = rc_root g v := by
      unfold rc_root
      rw [hLv]
    have e2 : rc_root g v = rc_root g p := huniq v p hLv hp
    rw [e1, e2]

private def rc_stableSetoid {V : Type*} {k : ℕ} (delta : V → Fin k → V) : Setoid V where
  r := rc_stable delta
  iseqv := ⟨rc_stable_refl delta, fun h => rc_stable_symm delta h,
    fun h1 h2 => rc_stable_trans delta h1 h2⟩

private def rc_quot {V : Type*} {k : ℕ} (delta : V → Fin k → V) :
    Quotient (rc_stableSetoid delta) → Fin k → Quotient (rc_stableSetoid delta) :=
  fun q c => Quotient.map' (fun v => delta v c)
    (fun _v _w h => rc_stable_foldl delta h [c]) q

private noncomputable instance rc_quotFintype {V : Type*} [Fintype V] {k : ℕ}
    (delta : V → Fin k → V) : Fintype (Quotient (rc_stableSetoid delta)) := by
  classical
  exact Quotient.fintype _

private instance rc_quotNonempty {V : Type*} [Nonempty V] {k : ℕ}
    (delta : V → Fin k → V) : Nonempty (Quotient (rc_stableSetoid delta)) :=
  ⟨Quotient.mk _ (Classical.choice ‹Nonempty V›)⟩

private theorem rc_translate_B_to_delta {V : Type*} {k : ℕ}
    (delta : V → Fin k → V)
    (sigma' : Quotient (rc_stableSetoid delta) → Equiv.Perm (Fin k))
    (u : List (Fin k)) (x y : V) (hst : rc_stable delta x y) :
    ∃ u' : List (Fin k),
      List.foldl (rc_recolor delta (fun v => sigma' (Quotient.mk _ v))) x u =
        List.foldl delta x u' ∧
      List.foldl (rc_recolor delta (fun v => sigma' (Quotient.mk _ v))) y u =
        List.foldl delta y u' := by
  induction u generalizing x y with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons c t ih =>
    have hclass : Quotient.mk (rc_stableSetoid delta) x = Quotient.mk _ y :=
      Quotient.sound hst
    have hsigP : sigma' (Quotient.mk _ y) = sigma' (Quotient.mk _ x) := by
      rw [hclass]
    have hst1 : rc_stable delta (delta x (sigma' (Quotient.mk _ x) c))
        (delta y (sigma' (Quotient.mk _ x) c)) :=
      rc_stable_foldl delta hst [sigma' (Quotient.mk _ x) c]
    obtain ⟨t', ht1, ht2⟩ := ih _ _ hst1
    refine ⟨sigma' (Quotient.mk _ x) c :: t', ?_, ?_⟩
    · change List.foldl (rc_recolor delta (fun v => sigma' (Quotient.mk _ v)))
          (delta x (sigma' (Quotient.mk _ x) c)) t =
        List.foldl delta (delta x (sigma' (Quotient.mk _ x) c)) t'
      exact ht1
    · change List.foldl (rc_recolor delta (fun v => sigma' (Quotient.mk _ v)))
          (delta y (sigma' (Quotient.mk _ y) c)) t =
        List.foldl delta (delta y (sigma' (Quotient.mk _ x) c)) t'
      rw [hsigP]
      exact ht2

private theorem rc_translate_delta_to_B {V : Type*} {k : ℕ}
    (delta : V → Fin k → V)
    (sigma' : Quotient (rc_stableSetoid delta) → Equiv.Perm (Fin k))
    (u' : List (Fin k)) (x y : V) (hst : rc_stable delta x y) :
    ∃ u : List (Fin k),
      List.foldl delta x u' =
        List.foldl (rc_recolor delta (fun v => sigma' (Quotient.mk _ v))) x u ∧
      List.foldl delta y u' =
        List.foldl (rc_recolor delta (fun v => sigma' (Quotient.mk _ v))) y u := by
  induction u' generalizing x y with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons d t' ih =>
    have hclass : Quotient.mk (rc_stableSetoid delta) x = Quotient.mk _ y :=
      Quotient.sound hst
    have hsigP : sigma' (Quotient.mk _ y) = sigma' (Quotient.mk _ x) := by
      rw [hclass]
    have hst1 : rc_stable delta (delta x d) (delta y d) :=
      rc_stable_foldl delta hst [d]
    obtain ⟨u_tail, ht1, ht2⟩ := ih _ _ hst1
    have hBxc : (rc_recolor delta (fun v => sigma' (Quotient.mk _ v))) x
        ((sigma' (Quotient.mk _ x)).symm d) = delta x d := by
      change delta x (sigma' (Quotient.mk _ x) ((sigma' (Quotient.mk _ x)).symm d)) =
        delta x d
      rw [Equiv.apply_symm_apply]
    have hByc : (rc_recolor delta (fun v => sigma' (Quotient.mk _ v))) y
        ((sigma' (Quotient.mk _ x)).symm d) = delta y d := by
      change delta y (sigma' (Quotient.mk _ y) ((sigma' (Quotient.mk _ x)).symm d)) =
        delta y d
      rw [hsigP, Equiv.apply_symm_apply]
    refine ⟨(sigma' (Quotient.mk _ x)).symm d :: u_tail, ?_, ?_⟩
    · change List.foldl delta (delta x d) t' =
        List.foldl (rc_recolor delta (fun v => sigma' (Quotient.mk _ v)))
          ((rc_recolor delta (fun v => sigma' (Quotient.mk _ v))) x
            ((sigma' (Quotient.mk _ x)).symm d)) u_tail
      rw [hBxc]
      exact ht1
    · change List.foldl delta (delta y d) t' =
        List.foldl (rc_recolor delta (fun v => sigma' (Quotient.mk _ v)))
          ((rc_recolor delta (fun v => sigma' (Quotient.mk _ v))) y
            ((sigma' (Quotient.mk _ x)).symm d)) u_tail
      rw [hByc]
      exact ht2

private theorem rc_stable_lift {V : Type*} {k : ℕ}
    (delta : V → Fin k → V)
    (sigma' : Quotient (rc_stableSetoid delta) → Equiv.Perm (Fin k))
    {x y : V} (hst : rc_stable delta x y) :
    rc_stable (rc_recolor delta (fun v => sigma' (Quotient.mk _ v))) x y := by
  intro u
  obtain ⟨u', hu1, hu2⟩ := rc_translate_B_to_delta delta sigma' u x y hst
  obtain ⟨v', hv⟩ := rc_stable_merge delta (rc_stable_foldl delta hst u')
  obtain ⟨v, hv1, hv2⟩ := rc_translate_delta_to_B delta sigma' v' _ _
    (rc_stable_foldl delta hst u')
  refine ⟨v, ?_⟩
  rw [List.foldl_append, List.foldl_append, hu1, hu2, ← hv1, ← hv2]
  exact hv

private def rc_isSSG {V : Type*} {k : ℕ} (delta : V → Fin k → V) (g : V → V) : Prop :=
  ∀ v : V, rc_adj delta v (g v)

private theorem rc_update_level_eq {V : Type*} [Finite V] [DecidableEq V]
    (R : V → V) (x y : V) (v : V) (havoid : ∀ i : ℕ, R^[i] v ≠ x) :
    rc_level (Function.update R x y) v = rc_level R v := by
  have agree : ∀ j : ℕ, (Function.update R x y)^[j] v = R^[j] v :=
    fun j => rc_update_iterate_agree R x y v havoid j
  have hz : ∀ i : ℕ, R^[i] (R^[rc_level R v] v) ≠ x := by
    intro i
    have e : R^[i] (R^[rc_level R v] v) = R^[rc_level R v + i] v := by
      rw [Nat.add_comm (rc_level R v) i, Function.iterate_add_apply]
    rw [e]
    exact havoid _
  have hagree2 : ∀ j : ℕ, (Function.update R x y)^[j]
      (R^[rc_level (Function.update R x y) v] v) = R^[j]
      (R^[rc_level (Function.update R x y) v] v) := by
    intro j
    have h1 := agree (rc_level (Function.update R x y) v + j)
    rw [Nat.add_comm (rc_level (Function.update R x y) v) j,
      Function.iterate_add_apply, Function.iterate_add_apply,
      agree (rc_level (Function.update R x y) v)] at h1
    exact h1
  have eL : (Function.update R x y)^[rc_level R v] v = R^[rc_level R v] v :=
    agree _
  have h1mem : R^[rc_level R v] v ∈ Function.periodicPts (Function.update R x y) :=
    rc_update_periodic R x y _ hz (rc_level_spec R v)
  rw [← eL] at h1mem
  have eL1 : (Function.update R x y)^[rc_level (Function.update R x y) v] v =
      R^[rc_level (Function.update R x y) v] v := agree _
  have hper1 : R^[rc_level (Function.update R x y) v] v ∈
      Function.periodicPts (Function.update R x y) := by
    rw [← eL1]
    exact rc_level_spec _ v
  exact Nat.le_antisymm
    (rc_level_le_of_mem _ _ h1mem)
    (rc_level_le_of_mem _ _ (rc_update_periodic_of R x y _ hagree2 hper1))

private theorem rc_level_along_orbit {V : Type*} [Finite V] (g : V → V) (v : V) :
    ∀ (i : ℕ), i ≤ rc_level g v →
    rc_level g (g^[i] v) = rc_level g v - i := by
  intro i
  induction i with
  | zero => intro _; simp only [Function.iterate_zero_apply, Nat.sub_zero]
  | succ i ih =>
    intro hi
    have hiL : i ≤ rc_level g v := by omega
    have eih := ih hiL
    have hnon : g^[i] v ∉ Function.periodicPts g := by
      intro hmem
      have h0 : rc_level g (g^[i] v) = 0 := (rc_level_zero_iff g _).mpr hmem
      omega
    have estep := rc_level_step g (g^[i] v) hnon
    have eiter : g^[i + 1] v = g (g^[i] v) := by
      rw [show i + 1 = (i).succ from rfl]
      exact Function.iterate_succ_apply' g i v
    rw [eiter, estep, eih]
    omega

private theorem rc_root_along_orbit {V : Type*} [Finite V] (g : V → V) (v : V)
    {i : ℕ} (hi : i ≤ rc_level g v) :
    rc_root g (g^[i] v) = rc_root g v := by
  unfold rc_root
  rw [rc_level_along_orbit g v i hi, ← Function.iterate_add_apply]
  have hii : rc_level g v - i + i = rc_level g v := by omega
  rw [hii]

private def rc_isBunch {V : Type*} {k : ℕ} (delta : V → Fin k → V) (x z : V) : Prop :=
  ∀ a : Fin k, delta x a = z

private theorem rc_height_gt_of_iterate_notMem {V : Type*} [Fintype V] [DecidableEq V]
    (g : V → V) (v : V) (L : ℕ) (h : g^[L] v ∉ Function.periodicPts g) :
    L < rc_height g := by
  by_contra hcon
  have h1 := rc_level_le_height g v
  have h2 : rc_height g ≤ L := by omega
  have hle : rc_level g v ≤ L := le_trans h1 h2
  exact h (rc_iterate_ge_level_periodic g v hle)

private theorem rc_path_point_notMem {V : Type*} [Finite V] (R : V → V) (p : V)
    {i : ℕ} (hi : i < rc_level R p) : R^[i] p ∉ Function.periodicPts R := by
  intro hmem
  have h0 : rc_level R (R^[i] p) = 0 := (rc_level_zero_iff R _).mpr hmem
  have hlev := rc_level_along_orbit R p i (by omega)
  omega

private theorem rc_root_of_mem_orbit {V : Type*} [Finite V] (R : V → V) (v x : V)
    (hmem : ∃ i : ℕ, R^[i] v = x) (hxnp : x ∉ Function.periodicPts R) :
    rc_root R x = rc_root R v := by
  obtain ⟨i, hi⟩ := hmem
  have hiL : i ≤ rc_level R v := by
    by_contra hcon
    have hle : rc_level R v ≤ i := by omega
    have h := rc_iterate_ge_level_periodic R v hle
    rw [hi] at h
    exact hxnp h
  have hroot := rc_root_along_orbit R v hiL
  rw [hi] at hroot
  exact hroot

private theorem rc_orbit_avoid_of_root_ne {V : Type*} [Finite V] (R : V → V) (v x : V)
    (hxnp : x ∉ Function.periodicPts R) (hne : rc_root R v ≠ rc_root R x) (i : ℕ) :
    R^[i] v ≠ x :=
  fun heq => hne (rc_root_of_mem_orbit R v x ⟨i, heq⟩ hxnp).symm

private noncomputable def rc_cycleFin {V : Type*} [DecidableEq V]
    (R : V → V) (r : V) : Finset V :=
  (Finset.range (Function.minimalPeriod R r)).image (fun t => R^[t] r)

private theorem rc_path_ne_of_lt {V : Type*} [Finite V] (R : V → V) (p : V) (L : ℕ)
    (hL : rc_level R p = L) {a b : ℕ} (ha : a < L) (hb : b < L) (hne : a ≠ b) :
    R^[a] p ≠ R^[b] p := by
  intro heq
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hxper : R^[a] p ∈ Function.periodicPts R := by
      refine Function.mem_periodicPts.mpr ⟨b - a, by omega, ?_⟩
      have e : R^[b - a] (R^[a] p) = R^[b] p := by
        have hdec : b = (b - a) + a := by omega
        conv_rhs => rw [hdec]
        exact (Function.iterate_add_apply R (b - a) a p).symm
      rw [← heq] at e
      exact e
    exact rc_path_point_notMem R p (by omega) hxper
  · have hxper : R^[b] p ∈ Function.periodicPts R := by
      refine Function.mem_periodicPts.mpr ⟨a - b, by omega, ?_⟩
      have e : R^[a - b] (R^[b] p) = R^[a] p := by
        have hdec : a = (a - b) + b := by omega
        conv_rhs => rw [hdec]
        exact (Function.iterate_add_apply R (a - b) b p).symm
      rw [heq] at e
      exact e
    exact rc_path_point_notMem R p (by omega) hxper

private theorem rc_Zpred_closed_tree {V : Type*} [Finite V] [DecidableEq V]
    (R : V → V) (p : V) (L : ℕ) (hL : rc_level R p = L)
    (j : ℕ) (x : V)
    (hxper : x ∈ Function.periodicPts R) (hrL : R^[L] p = rc_root R p)
    (s : ℕ) (hs : s < L) :
    ((∃ s' : ℕ, s' < L ∧ R^[s'] p = Function.update R x p (R^[s] p)) ∨
      (∃ t : ℕ, t ≤ j ∧ R^[t] (rc_root R p) = Function.update R x p (R^[s] p))) := by
  have hne : R^[s] p ≠ x := by
    intro heq
    have hnp : R^[s] p ∉ Function.periodicPts R :=
      rc_path_point_notMem R p (by omega)
    exact hnp (by rw [heq]; exact hxper)
  have eR' : Function.update R x p (R^[s] p) = R (R^[s] p) :=
    Function.update_of_ne hne _ _
  rw [eR']
  by_cases hsL : s + 1 < L
  · refine Or.inl ⟨s + 1, hsL, Function.iterate_succ_apply' R s p⟩
  · refine Or.inr ⟨0, Nat.zero_le j, ?_⟩
    have hsL' : s + 1 = L := by omega
    have e2 : R (R^[s] p) = R^[L] p := by
      rw [← hsL']
      exact (Function.iterate_succ_apply' R s p).symm
    rw [e2, hrL, Function.iterate_zero_apply]

private theorem rc_Zmem_cycle_le {V : Type*} [Finite V]
    (R : V → V) (p : V) (L : ℕ) (hL : rc_level R p = L)
    (j : ℕ) (hjm : j < Function.minimalPeriod R (rc_root R p))
    (hrper : rc_root R p ∈ Function.periodicPts R)
    (u : ℕ) (hum : u < Function.minimalPeriod R (rc_root R p))
    (hmem : ((∃ s : ℕ, s < L ∧ R^[s] p = R^[u] (rc_root R p)) ∨
      (∃ t : ℕ, t ≤ j ∧ R^[t] (rc_root R p) = R^[u] (rc_root R p)))) :
    u ≤ j := by
  rcases hmem with ⟨s, hs, heq⟩ | ⟨t, ht, heq⟩
  · exfalso
    have hnp : R^[s] p ∉ Function.periodicPts R :=
      rc_path_point_notMem R p (by omega)
    have hper : R^[s] p ∈ Function.periodicPts R := by
      rw [heq]
      exact rc_periodic_iterate R hrper u
    exact hnp hper
  · have htm : t < Function.minimalPeriod R (rc_root R p) := by omega
    have htu : t = u :=
      Function.iterate_injOn_Iio_minimalPeriod htm hum heq
    omega

private theorem rc_R'_agree_tree {V : Type*} [Finite V] [DecidableEq V]
    (R : V → V) (p : V) (L : ℕ) (hL : rc_level R p = L)
    (x : V) (hxper : x ∈ Function.periodicPts R) :
    ∀ s : ℕ, s ≤ L → (Function.update R x p)^[s] p = R^[s] p := by
  intro s
  induction s with
  | zero => intro _; rfl
  | succ s ih =>
    intro hs
    have hs' : s ≤ L := by omega
    have ih' := ih hs'
    have hne : R^[s] p ≠ x := by
      intro heq
      have hnp : R^[s] p ∉ Function.periodicPts R :=
        rc_path_point_notMem R p (show s < rc_level R p by omega)
      exact hnp (by rw [heq]; exact hxper)
    have e1 : (Function.update R x p)^[s + 1] p =
        Function.update R x p ((Function.update R x p)^[s] p) := by
      rw [show s + 1 = s.succ from rfl]
      exact Function.iterate_succ_apply' _ _ _
    have e2 : R^[s + 1] p = R (R^[s] p) := by
      rw [show s + 1 = s.succ from rfl]
      exact Function.iterate_succ_apply' _ _ _
    rw [e1, e2, ih', Function.update_of_ne hne]

private theorem rc_caseC_setup {V : Type*} [Finite V]
    (R : V → V) (p : V) (L : ℕ) (hL : rc_level R p = L)
    (x : V) (i : ℕ) (hi : R^[i] p = x) (hiL : L ≤ i) :
    ∃ j : ℕ, j < Function.minimalPeriod R (rc_root R p) ∧
      R^[j] (rc_root R p) = x ∧ x ∈ Function.periodicPts R := by
  have hxper : x ∈ Function.periodicPts R := by
    have h := rc_iterate_ge_level_periodic R p (show rc_level R p ≤ i by omega)
    rw [hi] at h
    exact h
  have hrL : R^[L] p = rc_root R p := by
    unfold rc_root
    rw [hL]
  have hxp : R^[i - L] (rc_root R p) = x := by
    have e : R^[i] p = R^[i - L] (R^[L] p) := by
      have hdec : i = (i - L) + L := by omega
      conv_lhs => rw [hdec]
      exact Function.iterate_add_apply R (i - L) L p
    rw [hi, hrL] at e
    exact e.symm
  refine ⟨(i - L) % Function.minimalPeriod R (rc_root R p), ?_, ?_, hxper⟩
  · exact Nat.mod_lt _ (Function.minimalPeriod_pos_of_mem_periodicPts
      (rc_root_periodic R p))
  · have e : R^[(i - L) % Function.minimalPeriod R (rc_root R p)] (rc_root R p) =
        R^[i - L] (rc_root R p) :=
      Function.iterate_mod_minimalPeriod_eq
    rw [e]
    exact hxp

private theorem rc_caseC1 {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (delta : V → Fin k → V) (R : V → V) (hR : rc_isSSG delta R)
    (hHmax : ∀ g : V → V, rc_isSSG delta g → rc_height g ≤ rc_height R)
    (L : ℕ) (hL : rc_height R = L) (hH : 1 ≤ L)
    (p : V) (hp : rc_level R p = L)
    (j : ℕ) (hjm : j < Function.minimalPeriod R (rc_root R p))
    (x : V) (hx : rc_adj delta x p) (hxj : R^[j] (rc_root R p) = x)
    (hxper : x ∈ Function.periodicPts R)
    (hC1 : L + j + 1 < Function.minimalPeriod R (rc_root R p)) :
    False := by
  have hrper : rc_root R p ∈ Function.periodicPts R := rc_root_periodic R p
  have hrL : R^[L] p = rc_root R p := by
    unfold rc_root
    rw [hp]
  set y := R^[j + 1] (rc_root R p) with hy
  have hj1m : j + 1 < Function.minimalPeriod R (rc_root R p) := by omega
  have hagree_y : ∀ s : ℕ, s ≤ Function.minimalPeriod R (rc_root R p) - j - 1 →
      (Function.update R x p)^[s] y = R^[s] y := by
    intro s
    induction s with
    | zero => intro _; rfl
    | succ s ih =>
      intro hs
      have hs' : s ≤ Function.minimalPeriod R (rc_root R p) - j - 1 := by omega
      have ih' := ih hs'
      have hne : R^[s] y ≠ x := by
        intro heq
        have e : R^[s] y = R^[j + 1 + s] (rc_root R p) := by
          rw [hy]
          have hdec : j + 1 + s = s + (j + 1) := by omega
          rw [hdec]
          exact (Function.iterate_add_apply R s (j + 1) _).symm
        rw [e, ← hxj] at heq
        have h1 : j + 1 + s < Function.minimalPeriod R (rc_root R p) := by omega
        exact (by omega : j + 1 + s ≠ j)
          (Function.iterate_injOn_Iio_minimalPeriod h1 hjm heq)
      have e1 : (Function.update R x p)^[s + 1] y =
          Function.update R x p ((Function.update R x p)^[s] y) := by
        rw [show s + 1 = s.succ from rfl]
        exact Function.iterate_succ_apply' _ _ _
      have e2 : R^[s + 1] y = R (R^[s] y) := by
        rw [show s + 1 = s.succ from rfl]
        exact Function.iterate_succ_apply' _ _ _
      rw [e1, e2, ih', Function.update_of_ne hne]
  have hY : (Function.update R x p)^[Function.minimalPeriod R (rc_root R p) - j - 1] y =
      rc_root R p := by
    rw [hagree_y _ le_rfl]
    have e : R^[Function.minimalPeriod R (rc_root R p) - j - 1] y =
        R^[Function.minimalPeriod R (rc_root R p)] (rc_root R p) := by
      rw [hy]
      have hdec : Function.minimalPeriod R (rc_root R p) =
          (Function.minimalPeriod R (rc_root R p) - j - 1) + (j + 1) := by omega
      conv_rhs => rw [hdec]
      exact (Function.iterate_add_apply R
        (Function.minimalPeriod R (rc_root R p) - j - 1) (j + 1) _).symm
    rw [e]
    have hmper : R^[Function.minimalPeriod R (rc_root R p)] (rc_root R p) =
        rc_root R p :=
      Function.iterate_minimalPeriod
    exact hmper
  have hagree_r : ∀ s : ℕ, s ≤ j →
      (Function.update R x p)^[s] (rc_root R p) = R^[s] (rc_root R p) :=
    fun s hs => rc_R'_agree_cycle R _ j hjm x p hxj s hs
  have e2a : (Function.update R x p)^[j] (rc_root R p) = x := by
    rw [rc_R'_agree_cycle R _ j hjm x p hxj j le_rfl]
    exact hxj
  have e2 : (Function.update R x p)^[j + 1] (rc_root R p) = p := by
    have e : (Function.update R x p)^[j + 1] (rc_root R p) =
        Function.update R x p ((Function.update R x p)^[j] (rc_root R p)) := by
      rw [show j + 1 = j.succ from rfl]
      exact Function.iterate_succ_apply' _ _ _
    rw [e, e2a]
    exact Function.update_self _ _ _
  have e3 : (Function.update R x p)^[L] p = rc_root R p := by
    rw [rc_R'_agree_tree R p L hp x hxper L le_rfl, hrL]
  have hrper' : rc_root R p ∈ Function.periodicPts (Function.update R x p) := by
    refine Function.mem_periodicPts.mpr ⟨j + 1 + L, by omega, ?_⟩
    have e1 : (Function.update R x p)^[j + 1 + L] (rc_root R p) =
        (Function.update R x p)^[L] ((Function.update R x p)^[j + 1] (rc_root R p)) := by
      have hdec : j + 1 + L = L + (j + 1) := by omega
      rw [hdec]
      exact Function.iterate_add_apply _ _ _ _
    have hret : (Function.update R x p)^[j + 1 + L] (rc_root R p) = rc_root R p := by
      rw [e1, e2]
      exact e3
    exact hret
  have hlev_y : rc_level (Function.update R x p) y =
      Function.minimalPeriod R (rc_root R p) - j - 1 := by
    apply le_antisymm
    · exact rc_level_le_of_mem _ _ (by rw [hY]; exact hrper')
    · by_contra hcon
      have hlt : rc_level (Function.update R x p) y <
          Function.minimalPeriod R (rc_root R p) - j - 1 := by omega
      have hspec := rc_level_spec (Function.update R x p) y
      have hle : rc_level (Function.update R x p) y ≤
          Function.minimalPeriod R (rc_root R p) - j - 1 := by omega
      have eag : (Function.update R x p)^[rc_level (Function.update R x p) y] y =
          R^[rc_level (Function.update R x p) y] y :=
        hagree_y _ hle
      have hPclosed : ∀ a : V,
          (∃ t : ℕ, (Function.update R x p)^[t] (rc_root R p) = a) →
          ∃ t : ℕ, (Function.update R x p)^[t] (rc_root R p) =
            Function.update R x p a := by
        intro a ⟨t, ht⟩
        refine ⟨t + 1, ?_⟩
        have e : (Function.update R x p)^[t + 1] (rc_root R p) =
            Function.update R x p ((Function.update R x p)^[t] (rc_root R p)) := by
          rw [show t + 1 = t.succ from rfl]
          exact Function.iterate_succ_apply' _ _ _
        rw [e, ht]
      have hmemP : (∃ t : ℕ, (Function.update R x p)^[t] (rc_root R p) =
          (Function.update R x p)^[Function.minimalPeriod R (rc_root R p) - j - 1 -
            rc_level (Function.update R x p) y]
            ((Function.update R x p)^[rc_level (Function.update R x p) y] y)) := by
        have e : (Function.update R x p)^[Function.minimalPeriod R (rc_root R p) - j - 1 -
              rc_level (Function.update R x p) y]
              ((Function.update R x p)^[rc_level (Function.update R x p) y] y) =
            (Function.update R x p)^[Function.minimalPeriod R (rc_root R p) - j - 1] y := by
          rw [← Function.iterate_add_apply, Nat.sub_add_cancel hle]
        rw [e, hY]
        refine ⟨0, ?_⟩
        simp
      have hconP := rc_mem_of_periodic_iterate_mem _ _ hPclosed _ hspec _ hmemP
      obtain ⟨t, ht⟩ := hconP
      have hZall : ∀ u : ℕ,
          ((∃ s : ℕ, s < L ∧ R^[s] p = (Function.update R x p)^[u] (rc_root R p)) ∨
            (∃ w : ℕ, w ≤ j ∧ R^[w] (rc_root R p) =
              (Function.update R x p)^[u] (rc_root R p))) := by
        intro u
        induction u with
        | zero =>
          refine Or.inr ⟨0, Nat.zero_le j, ?_⟩
          simp
        | succ u ih =>
          have e : (Function.update R x p)^[u + 1] (rc_root R p) =
              Function.update R x p ((Function.update R x p)^[u] (rc_root R p)) := by
            rw [show u + 1 = u.succ from rfl]
            exact Function.iterate_succ_apply' _ _ _
          rw [e]
          rcases ih with ⟨s, hs, heq⟩ | ⟨w, hw, heq⟩
          · have h := rc_Zpred_closed_tree R p L hp j x hxper hrL s hs
            rw [heq] at h
            exact h
          · have h := rc_Zpred_closed_cycle R p L j hjm x hxj hH w hw
            rw [heq] at h
            exact h
      have hZt := hZall t
      rw [ht] at hZt
      have epos : (Function.update R x p)^[rc_level (Function.update R x p) y] y =
          R^[j + 1 + rc_level (Function.update R x p) y] (rc_root R p) := by
        rw [eag]
        have e1 : R^[rc_level (Function.update R x p) y] y =
            R^[rc_level (Function.update R x p) y] (R^[j + 1] (rc_root R p)) :=
          congrArg _ hy
        have hdec : j + 1 + rc_level (Function.update R x p) y =
            rc_level (Function.update R x p) y + (j + 1) := by omega
        rw [hdec, e1]
        exact (Function.iterate_add_apply R _ _ _).symm
      rw [epos] at hZt
      have hpos : j + 1 + rc_level (Function.update R x p) y <
          Function.minimalPeriod R (rc_root R p) := by omega
      have hle2 := rc_Zmem_cycle_le R p L hp j hjm hrper _ hpos hZt
      omega
  have hgt : L < rc_height (Function.update R x p) := by
    have h1 := rc_level_le_height (Function.update R x p) y
    omega
  have hle := hHmax _ (rc_ssg_update_edge delta R hR x p hx)
  omega

private theorem rc_R'_to_root {V : Type*} [Finite V] [DecidableEq V]
    (R : V → V) (p : V) (L : ℕ) (hL : rc_level R p = L)
    (x : V) (hxper : x ∈ Function.periodicPts R) :
    (Function.update R x p)^[L] p = rc_root R p := by
  have hrL : R^[L] p = rc_root R p := by
    unfold rc_root
    rw [hL]
  rw [rc_R'_agree_tree R p L hL x hxper L le_rfl, hrL]

private theorem rc_caseC2_tree_per {V : Type*} [Finite V] [DecidableEq V]
    (R : V → V) (p : V) (L : ℕ) (hp : rc_level R p = L)
    (j : ℕ) (hjm : j < Function.minimalPeriod R (rc_root R p))
    (x : V) (hxj : R^[j] (rc_root R p) = x)
    (hxper : x ∈ Function.periodicPts R)
    (s : ℕ) (hs : s < L) :
    R^[s] p ∈ Function.periodicPts (Function.update R x p) := by
  have hpos : 0 < L + j + 1 := by omega
  refine Function.mem_periodicPts.mpr ⟨L + j + 1, hpos, ?_⟩
  have step1 : (Function.update R x p)^[L - s] (R^[s] p) = rc_root R p := by
    have a1 := rc_R'_agree_tree R p L hp x hxper s (by omega)
    have a2 := rc_R'_to_root R p L hp x hxper
    have hdec : L = (L - s) + s := by omega
    have e : (Function.update R x p)^[L] p =
        (Function.update R x p)^[L - s] ((Function.update R x p)^[s] p) := by
      conv_lhs => rw [hdec]
      exact Function.iterate_add_apply _ _ _ _
    rw [e, a1] at a2
    exact a2
  have step2 : (Function.update R x p)^[(L - s) + (j + 1)] (R^[s] p) = p := by
    have e : (Function.update R x p)^[(L - s) + (j + 1)] (R^[s] p) =
        (Function.update R x p)^[j + 1]
          ((Function.update R x p)^[L - s] (R^[s] p)) := by
      have hdec : (L - s) + (j + 1) = (j + 1) + (L - s) := by omega
      conv_lhs => rw [hdec]
      exact Function.iterate_add_apply _ _ _ _
    rw [e, step1]
    exact rc_R'_to_p R _ j hjm x p hxj
  have hdec : L + j + 1 = s + ((L - s) + (j + 1)) := by omega
  have e : (Function.update R x p)^[L + j + 1] (R^[s] p) =
      (Function.update R x p)^[s]
        ((Function.update R x p)^[(L - s) + (j + 1)] (R^[s] p)) := by
    conv_lhs => rw [hdec]
    exact Function.iterate_add_apply _ _ _ _
  have hfin : (Function.update R x p)^[L + j + 1] (R^[s] p) = R^[s] p := by
    rw [e, step2]
    exact rc_R'_agree_tree R p L hp x hxper s (by omega)
  exact hfin

private theorem rc_caseC2_seg_per {V : Type*} [Finite V] [DecidableEq V]
    (R : V → V) (p : V) (L : ℕ) (hp : rc_level R p = L)
    (j : ℕ) (hjm : j < Function.minimalPeriod R (rc_root R p))
    (x : V) (hxj : R^[j] (rc_root R p) = x)
    (hxper : x ∈ Function.periodicPts R)
    (t : ℕ) (ht : t ≤ j) :
    R^[t] (rc_root R p) ∈ Function.periodicPts (Function.update R x p) := by
  have hpos : 0 < L + j + 1 := by omega
  refine Function.mem_periodicPts.mpr ⟨L + j + 1, hpos, ?_⟩
  have step1 : (Function.update R x p)^[j - t] (R^[t] (rc_root R p)) = x := by
    have a1 := rc_R'_agree_cycle R _ j hjm x p hxj t ht
    have a2 : (Function.update R x p)^[j] (rc_root R p) = x := by
      rw [rc_R'_agree_cycle R _ j hjm x p hxj j le_rfl]
      exact hxj
    have hdec : j = (j - t) + t := by omega
    have e : (Function.update R x p)^[j] (rc_root R p) =
        (Function.update R x p)^[j - t]
          ((Function.update R x p)^[t] (rc_root R p)) := by
      conv_lhs => rw [hdec]
      exact Function.iterate_add_apply _ _ _ _
    rw [e, a1] at a2
    exact a2
  have step2 : (Function.update R x p)^[(j - t) + 1] (R^[t] (rc_root R p)) = p := by
    have e : (Function.update R x p)^[(j - t) + 1] (R^[t] (rc_root R p)) =
        Function.update R x p
          ((Function.update R x p)^[j - t] (R^[t] (rc_root R p))) := by
      rw [show (j - t) + 1 = ((j - t)).succ from rfl]
      exact Function.iterate_succ_apply' _ _ _
    rw [e, step1]
    exact Function.update_self _ _ _
  have step3 : (Function.update R x p)^[(j - t) + 1 + L] (R^[t] (rc_root R p)) =
      rc_root R p := by
    have e : (Function.update R x p)^[(j - t) + 1 + L] (R^[t] (rc_root R p)) =
        (Function.update R x p)^[L]
          ((Function.update R x p)^[(j - t) + 1] (R^[t] (rc_root R p))) := by
      have hdec : (j - t) + 1 + L = L + ((j - t) + 1) := by omega
      conv_lhs => rw [hdec]
      exact Function.iterate_add_apply _ _ _ _
    rw [e, step2]
    exact rc_R'_to_root R p L hp x hxper
  have hdec : L + j + 1 = t + ((j - t) + 1 + L) := by omega
  have e : (Function.update R x p)^[L + j + 1] (R^[t] (rc_root R p)) =
      (Function.update R x p)^[t]
        ((Function.update R x p)^[(j - t) + 1 + L] (R^[t] (rc_root R p))) := by
    conv_lhs => rw [hdec]
    exact Function.iterate_add_apply _ _ _ _
  have hfin : (Function.update R x p)^[L + j + 1] (R^[t] (rc_root R p)) =
      R^[t] (rc_root R p) := by
    rw [e, step3]
    exact rc_R'_agree_cycle R _ j hjm x p hxj t ht
  exact hfin

private theorem rc_caseC2_qagree {V : Type*} [Finite V] [DecidableEq V]
    (R : V → V) (q : V) (L : ℕ) (hq_top : rc_level R q = L)
    (x p : V) (hxper : x ∈ Function.periodicPts R) :
    ∀ s : ℕ, s ≤ L → (Function.update R x p)^[s] q = R^[s] q := by
  apply rc_update_agree_upto R x p q L _
  intro s' hs' heq
  have hnp : R^[s'] q ∉ Function.periodicPts R :=
    rc_path_point_notMem R q (show s' < rc_level R q by omega)
  exact hnp (by rw [heq]; exact hxper)

private theorem rc_caseC2_offcycle {V : Type*} [Finite V] [DecidableEq V]
    (R : V → V) (L : ℕ) (p : V)
    (q : V) (hq_top : rc_level R q = L)
    (j : ℕ) (hjm : j < Function.minimalPeriod R (rc_root R p))
    (x : V) (hxj : R^[j] (rc_root R p) = x)
    (hxper : x ∈ Function.periodicPts R)
    (hqC : rc_root R q ∉ rc_cycleFin R (rc_root R p)) :
    rc_level (Function.update R x p) q = L := by
  have hrper : rc_root R p ∈ Function.periodicPts R := rc_root_periodic R p
  have havoid : ∀ i : ℕ, R^[i] q ≠ x := by
    intro i heq
    by_cases hiL : i < L
    · have hnp : R^[i] q ∉ Function.periodicPts R :=
        rc_path_point_notMem R q (show i < rc_level R q by omega)
      exact hnp (by rw [heq]; exact hxper)
    · have hper_i : R^[i] q ∈ Function.periodicPts R :=
        rc_iterate_ge_level_periodic R q (show rc_level R q ≤ i by omega)
      have e : R^[i] q = R^[i - L] (rc_root R q) := by
        have hLq : R^[L] q = rc_root R q := by
          unfold rc_root
          rw [hq_top]
        have hdec : i = (i - L) + L := by omega
        conv_lhs => rw [hdec]
        rw [← hLq]
        exact Function.iterate_add_apply R (i - L) L q
      have hmem : R^[i - L] (rc_root R q) ∈ rc_cycleFin R (rc_root R p) := by
        rw [← e, heq]
        exact (rc_cycleFin_mem R _ _).mpr ⟨j, hjm, hxj⟩
      exact hqC (rc_cycleFin_absorb R _ hrper _ (rc_root_periodic R q) _ hmem)
  have hlev : rc_level (Function.update R x p) q = L := by
    rw [rc_update_level_eq R x p q havoid]
    exact hq_top
  exact hlev

private theorem rc_caseC2_oncycle_gt {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (delta : V → Fin k → V) (R : V → V) (hR : rc_isSSG delta R)
    (hHmax : ∀ g : V → V, rc_isSSG delta g → rc_height g ≤ rc_height R)
    (L : ℕ) (hL : rc_height R = L) (hH : 1 ≤ L)
    (p : V) (hp : rc_level R p = L)
    (q : V) (hq_top : rc_level R q = L)
    (j : ℕ) (hjm : j < Function.minimalPeriod R (rc_root R p))
    (x : V) (hx : rc_adj delta x p) (hxj : R^[j] (rc_root R p) = x)
    (hxper : x ∈ Function.periodicPts R)
    (t : ℕ) (htm : t < Function.minimalPeriod R (rc_root R p))
    (htq : R^[t] (rc_root R p) = rc_root R q) (hgt : j < t) :
    False := by
  have hrper : rc_root R p ∈ Function.periodicPts R := rc_root_periodic R p
  have hrL : R^[L] p = rc_root R p := by
    unfold rc_root
    rw [hp]
  have hLq : R^[L] q = rc_root R q := by
    unfold rc_root
    rw [hq_top]
  have hagT : ∀ s : ℕ, s ≤ Function.minimalPeriod R (rc_root R p) - t →
      (Function.update R x p)^[s] (R^[t] (rc_root R p)) =
        R^[s] (R^[t] (rc_root R p)) := by
    apply rc_update_agree_upto R x p _ (Function.minimalPeriod R (rc_root R p) - t) _
    intro s' hs' heq
    have e : R^[s'] (R^[t] (rc_root R p)) = R^[t + s'] (rc_root R p) := by
      have hdec : t + s' = s' + t := by omega
      rw [hdec]
      exact (Function.iterate_add_apply R s' t _).symm
    rw [e, ← hxj] at heq
    have h1 : t + s' < Function.minimalPeriod R (rc_root R p) := by omega
    exact (by omega : t + s' ≠ j)
      (Function.iterate_injOn_Iio_minimalPeriod h1 hjm heq)
  have hland : (Function.update R x p)^[Function.minimalPeriod R (rc_root R p) - t]
      (R^[t] (rc_root R p)) = rc_root R p := by
    rw [hagT _ le_rfl]
    have e : R^[Function.minimalPeriod R (rc_root R p) - t] (R^[t] (rc_root R p)) =
        R^[Function.minimalPeriod R (rc_root R p)] (rc_root R p) := by
      have hdec : Function.minimalPeriod R (rc_root R p) =
          (Function.minimalPeriod R (rc_root R p) - t) + t := by omega
      conv_rhs => rw [hdec]
      exact (Function.iterate_add_apply R
        (Function.minimalPeriod R (rc_root R p) - t) t _).symm
    rw [e]
    exact Function.iterate_minimalPeriod
  have hclosedZ : ∀ a : V, ((∃ s : ℕ, s < L ∧ R^[s] p = a) ∨
      (∃ w : ℕ, w ≤ j ∧ R^[w] (rc_root R p) = a)) →
      ((∃ s : ℕ, s < L ∧ R^[s] p = Function.update R x p a) ∨
        (∃ w : ℕ, w ≤ j ∧ R^[w] (rc_root R p) = Function.update R x p a)) := by
    intro a ha
    rcases ha with ⟨s, hs, heq⟩ | ⟨w, hw, heq⟩
    · have h := rc_Zpred_closed_tree R p L hp j x hxper hrL s hs
      rw [heq] at h
      exact h
    · have h := rc_Zpred_closed_cycle R p L j hjm x hxj hH w hw
      rw [heq] at h
      exact h
  have hLq' : (Function.update R x p)^[L] q = R^[t] (rc_root R p) := by
    rw [rc_caseC2_qagree R q L hq_top x p hxper L le_rfl, hLq, ← htq]
  have hnper : (Function.update R x p)^[L] q ∉
      Function.periodicPts (Function.update R x p) := by
    intro hmem
    have hmemZ : ((∃ s : ℕ, s < L ∧ R^[s] p =
        (Function.update R x p)^[Function.minimalPeriod R (rc_root R p) - t]
          ((Function.update R x p)^[L] q)) ∨
        (∃ w : ℕ, w ≤ j ∧ R^[w] (rc_root R p) =
          (Function.update R x p)^[Function.minimalPeriod R (rc_root R p) - t]
            ((Function.update R x p)^[L] q))) := by
      rw [hLq', hland]
      exact Or.inr ⟨0, Nat.zero_le j, by simp⟩
    have hZP := rc_mem_of_periodic_iterate_mem _ _ hclosedZ _ hmem _ hmemZ
    rcases hZP with ⟨s, hs, heq⟩ | ⟨w, hw, heq⟩
    · have hnp : R^[s] p ∉ Function.periodicPts R :=
        rc_path_point_notMem R p (by omega)
      rw [hLq'] at heq
      have hper : R^[s] p ∈ Function.periodicPts R := by
        rw [heq]
        exact rc_periodic_iterate R hrper t
      exact hnp hper
    · rw [hLq'] at heq
      have hwm : w < Function.minimalPeriod R (rc_root R p) := by omega
      have hwt : w = t :=
        Function.iterate_injOn_Iio_minimalPeriod hwm htm heq
      omega
  have hlev : L < rc_level (Function.update R x p) q := by
    by_contra hcon
    have hle : rc_level (Function.update R x p) q ≤ L := by omega
    exact hnper (rc_iterate_ge_level_periodic _ _ hle)
  have hgt2 : L < rc_height (Function.update R x p) := by
    have h1 := rc_level_le_height (Function.update R x p) q
    omega
  have hle := hHmax _ (rc_ssg_update_edge delta R hR x p hx)
  omega

private theorem rc_caseC2_cyc {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V) (L : ℕ)
    (p : V) (hp : rc_level R p = L)
    (j : ℕ) (hjm : j < Function.minimalPeriod R (rc_root R p))
    (x : V) (hxj : R^[j] (rc_root R p) = x)
    (hperT : ∀ s : ℕ, s < L →
      R^[s] p ∈ Function.periodicPts (Function.update R x p))
    (hperS : ∀ t : ℕ, t ≤ j →
      R^[t] (rc_root R p) ∈ Function.periodicPts (Function.update R x p))
    (hC2 : Function.minimalPeriod R (rc_root R p) < L + j + 1) :
    rc_cyc R < rc_cyc (Function.update R x p) := by
  classical
  have hrper : rc_root R p ∈ Function.periodicPts R := rc_root_periodic R p
  have hCcard : (rc_cycleFin R (rc_root R p)).card =
      Function.minimalPeriod R (rc_root R p) := rc_cycleFin_card _ _
  have hCsub : rc_cycleFin R (rc_root R p) ⊆
      Finset.univ.filter (fun v => v ∈ Function.periodicPts R) := by
    intro z hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ z, ?_⟩
    obtain ⟨t, ht, rfl⟩ := (rc_cycleFin_mem R _ _).mp hz
    exact rc_periodic_iterate R hrper t
  have hTinj : Set.InjOn (fun s => R^[s] p) ↑(Finset.range L) := by
    intro a ha b hb hab
    have ha' : a < L := Finset.mem_range.mp (Finset.mem_coe.mp ha)
    have hb' : b < L := Finset.mem_range.mp (Finset.mem_coe.mp hb)
    by_contra hne
    exact rc_path_ne_of_lt R p L hp ha' hb' hne hab
  have hTcard : ((Finset.range L).image (fun s => R^[s] p)).card = L := by
    rw [Finset.card_image_of_injOn hTinj, Finset.card_range]
  have hSinj : Set.InjOn (fun t => R^[t] (rc_root R p))
      ↑(Finset.range (j + 1)) := by
    intro a ha b hb hab
    have ha' : a < j + 1 := Finset.mem_range.mp (Finset.mem_coe.mp ha)
    have hb' : b < j + 1 := Finset.mem_range.mp (Finset.mem_coe.mp hb)
    have ham : a < Function.minimalPeriod R (rc_root R p) := by omega
    have hbm : b < Function.minimalPeriod R (rc_root R p) := by omega
    exact Function.iterate_injOn_Iio_minimalPeriod ham hbm hab
  have hScard : ((Finset.range (j + 1)).image
      (fun t => R^[t] (rc_root R p))).card = j + 1 := by
    rw [Finset.card_image_of_injOn hSinj, Finset.card_range]
  have hTSdisj : Disjoint ((Finset.range L).image (fun s => R^[s] p))
      ((Finset.range (j + 1)).image (fun t => R^[t] (rc_root R p))) := by
    rw [Finset.disjoint_left]
    intro z hzT hzS
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hzT
    obtain ⟨t, ht, htz⟩ := Finset.mem_image.mp hzS
    have hsm : s < L := Finset.mem_range.mp hs
    have hper : R^[s] p ∈ Function.periodicPts R := by
      rw [← htz]
      exact rc_periodic_iterate R hrper t
    exact rc_path_point_notMem R p (by omega) hper
  have hZcard : (((Finset.range L).image (fun s => R^[s] p)) ∪
      ((Finset.range (j + 1)).image (fun t => R^[t] (rc_root R p)))).card =
      L + (j + 1) := by
    rw [Finset.card_union_of_disjoint hTSdisj, hTcard, hScard]
  have hZsub : (((Finset.range L).image (fun s => R^[s] p)) ∪
      ((Finset.range (j + 1)).image (fun t => R^[t] (rc_root R p)))) ⊆
      Finset.univ.filter
        (fun v => v ∈ Function.periodicPts (Function.update R x p)) := by
    intro z hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ z, ?_⟩
    rcases Finset.mem_union.mp hz with hzT | hzS
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hzT
      exact hperT s (Finset.mem_range.mp hs)
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hzS
      have htm : t < j + 1 := Finset.mem_range.mp ht
      exact hperS t (by omega)
  have hSCsub : (Finset.univ.filter (fun v => v ∈ Function.periodicPts R)) \
      rc_cycleFin R (rc_root R p) ⊆
      Finset.univ.filter
        (fun v => v ∈ Function.periodicPts (Function.update R x p)) := by
    intro z hz
    have hzS := (Finset.mem_sdiff.mp hz).1
    have hzC := (Finset.mem_sdiff.mp hz).2
    have hzp : z ∈ Function.periodicPts R := (Finset.mem_filter.mp hzS).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ z, ?_⟩
    apply rc_update_periodic R x p z _ hzp
    intro i heq
    have hxC : x ∈ rc_cycleFin R (rc_root R p) :=
      (rc_cycleFin_mem R _ _).mpr ⟨j, hjm, hxj⟩
    have hmem : R^[i] z ∈ rc_cycleFin R (rc_root R p) := by
      rw [heq]
      exact hxC
    exact hzC (rc_cycleFin_absorb R _ hrper z hzp i hmem)
  have hdisj : Disjoint ((Finset.univ.filter (fun v => v ∈ Function.periodicPts R)) \
      rc_cycleFin R (rc_root R p))
      (((Finset.range L).image (fun s => R^[s] p)) ∪
        ((Finset.range (j + 1)).image (fun t => R^[t] (rc_root R p)))) := by
    rw [Finset.disjoint_left]
    intro z hzSC hzZ
    have hzC : z ∉ rc_cycleFin R (rc_root R p) := (Finset.mem_sdiff.mp hzSC).2
    have hzP : z ∈ Function.periodicPts R :=
      (Finset.mem_filter.mp (Finset.mem_sdiff.mp hzSC).1).2
    rcases Finset.mem_union.mp hzZ with hzT | hzS
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hzT
      have hsm : s < L := Finset.mem_range.mp hs
      exact rc_path_point_notMem R p (by omega) hzP
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hzS
      have htm0 : t < j + 1 := Finset.mem_range.mp ht
      exact hzC ((rc_cycleFin_mem R _ _).mpr ⟨t, by omega, rfl⟩)
  have hUsub : (((Finset.univ.filter (fun v => v ∈ Function.periodicPts R)) \
      rc_cycleFin R (rc_root R p)) ∪
      (((Finset.range L).image (fun s => R^[s] p)) ∪
        ((Finset.range (j + 1)).image (fun t => R^[t] (rc_root R p))))) ⊆
      Finset.univ.filter
        (fun v => v ∈ Function.periodicPts (Function.update R x p)) :=
    Finset.union_subset hSCsub hZsub
  have hcard := Finset.card_le_card hUsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_sdiff_of_subset hCsub, hZcard,
    hCcard] at hcard
  unfold rc_cyc
  omega

private theorem rc_caseA_offorbit {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (delta : V → Fin k → V) (R : V → V) (hR : rc_isSSG delta R)
    (hHmax : ∀ g : V → V, rc_isSSG delta g → rc_height g ≤ rc_height R)
    (L : ℕ) (hL : rc_height R = L) (hH : 1 ≤ L)
    (p : V) (hp : rc_level R p = L)
    (x : V) (hx : rc_adj delta x p) (havoid : ∀ i : ℕ, R^[i] p ≠ x) :
    False := by
  classical
  have hR'ssg : rc_isSSG delta (Function.update R x p) :=
    rc_ssg_update_edge delta R hR x p hx
  have hRx : Function.update R x p x = p := Function.update_self _ _ _
  have hagree_p : ∀ s : ℕ, (Function.update R x p)^[s] p = R^[s] p :=
    fun s => rc_update_iterate_agree R x p p havoid s
  have hLp : (Function.update R x p)^[L] x = R^[L - 1] p := by
    have hdec : L = (L - 1) + 1 := by omega
    have e1 : (Function.update R x p)^[L] x =
        (Function.update R x p)^[L - 1] ((Function.update R x p) x) := by
      conv_lhs => rw [hdec]
      rw [Function.iterate_add_apply, rc_update_iterate_one]
    rw [e1, hRx, hagree_p]
  have hnper : R^[L - 1] p ∉ Function.periodicPts R := by
    intro hmem
    have h0 := (rc_level_zero_iff R _).mpr hmem
    have h := rc_level_along_orbit R p (L - 1) (by omega)
    omega
  have havoid2 : ∀ i : ℕ, R^[i] (R^[L - 1] p) ≠ x := by
    intro i heq
    have e : R^[i] (R^[L - 1] p) = R^[L - 1 + i] p := by
      rw [show L - 1 + i = i + (L - 1) from by omega]
      exact (Function.iterate_add_apply R i (L - 1) p).symm
    rw [e] at heq
    exact havoid _ heq
  have hnper' : R^[L - 1] p ∉ Function.periodicPts (Function.update R x p) := by
    intro hmem
    apply hnper
    exact rc_update_periodic_of R x p _
      (fun j => rc_update_iterate_agree R x p _ havoid2 j) hmem
  have hgt : L < rc_height (Function.update R x p) :=
    rc_height_gt_of_iterate_notMem _ x L (by rwa [hLp])
  have hle := hHmax _ hR'ssg
  omega

private theorem rc_caseB_tree {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (delta : V → Fin k → V) (R : V → V) (hR : rc_isSSG delta R)
    (hHmax : ∀ g : V → V, rc_isSSG delta g → rc_height g ≤ rc_height R)
    (hCmax : ∀ g : V → V, rc_isSSG delta g → rc_height g = rc_height R →
      rc_cyc g ≤ rc_cyc R)
    (L : ℕ) (hL : rc_height R = L) (hH : 1 ≤ L)
    (p : V) (hp : rc_level R p = L)
    (q : V) (hq_top : rc_level R q = L) (hq_root : rc_root R q ≠ rc_root R p)
    (x : V) (hx : rc_adj delta x p)
    (i : ℕ) (hi : R^[i] p = x) (hiL : i < L) :
    False := by
  classical
  have hxnp : x ∉ Function.periodicPts R := by
    rw [← hi]
    exact rc_path_point_notMem R p (by omega)
  have hpnp : p ∉ Function.periodicPts R := by
    intro hmem
    have h0 := (rc_level_zero_iff R p).mpr hmem
    omega
  have hR'ssg : rc_isSSG delta (Function.update R x p) :=
    rc_ssg_update_edge delta R hR x p hx
  have hRx : Function.update R x p x = p := Function.update_self _ _ _
  have hagree : ∀ s : ℕ, s ≤ i → (Function.update R x p)^[s] p = R^[s] p := by
    apply rc_update_agree_upto R x p p i _
    intro s hs heq
    exact rc_path_ne_of_lt R p L hp (by omega) hiL (by omega) (heq.trans hi.symm)
  have hRip : (Function.update R x p)^[i] p = x := by
    rw [hagree i le_rfl, hi]
  have hper_p' : p ∈ Function.periodicPts (Function.update R x p) := by
    refine Function.mem_periodicPts.mpr ⟨i + 1, by omega, ?_⟩
    change (Function.update R x p)^[i + 1] p = p
    have e : (Function.update R x p)^[i + 1] p =
        Function.update R x p ((Function.update R x p)^[i] p) := by
      rw [show i + 1 = i.succ from rfl]
      exact Function.iterate_succ_apply' _ i p
    rw [e, hRip, hRx]
  have hsub : ∀ z : V, z ∈ Function.periodicPts R →
      z ∈ Function.periodicPts (Function.update R x p) := by
    intro z hz
    refine rc_update_periodic R x p z ?_ hz
    intro t heq
    have h1 := rc_periodic_iterate R hz t
    rw [heq] at h1
    exact hxnp h1
  have hcyc : rc_cyc R < rc_cyc (Function.update R x p) :=
    rc_cyc_gt_of_subset_ne R _ hsub p hper_p' hpnp
  have hrootx : rc_root R x = rc_root R p := by
    rw [← hi]
    exact rc_root_along_orbit R p (by omega)
  have hneq : rc_root R q ≠ rc_root R x := by
    rw [hrootx]
    exact hq_root
  have havoid_q : ∀ t : ℕ, R^[t] q ≠ x := by
    intro t
    exact rc_orbit_avoid_of_root_ne R q x hxnp hneq t
  have hlevq : rc_level (Function.update R x p) q = L := by
    rw [rc_update_level_eq R x p q havoid_q]
    exact hq_top
  have hght : L ≤ rc_height (Function.update R x p) := by
    have h1 := rc_level_le_height (Function.update R x p) q
    omega
  by_cases hgt : L < rc_height (Function.update R x p)
  · have hle := hHmax _ hR'ssg
    omega
  · have heqH : rc_height (Function.update R x p) = rc_height R := by omega
    have hle := hCmax _ hR'ssg heqH
    omega

private theorem rc_caseC2_oncycle_le {V : Type*} [Finite V] [DecidableEq V]
    (R : V → V) (p : V) (L : ℕ) (hp : rc_level R p = L) (hH : 1 ≤ L)
    (j : ℕ) (hjm : j < Function.minimalPeriod R (rc_root R p))
    (x : V) (hxj : R^[j] (rc_root R p) = x)
    (hxper : x ∈ Function.periodicPts R)
    (q : V) (hq_top : rc_level R q = L) (hq_root : rc_root R q ≠ rc_root R p)
    (s : ℕ) (hsj : s ≤ j)
    (hsq : R^[s] (rc_root R p) = rc_root R q) :
    rc_level (Function.update R x p) q = L := by
  classical
  have hrper : rc_root R p ∈ Function.periodicPts R := rc_root_periodic R p
  have hcP : x ∈ Function.periodicPts R := hxper
  have hnper_q : R^[L - 1] q ∉ Function.periodicPts R :=
    rc_path_point_notMem R q (by omega)
  have hLq : R^[L] q = rc_root R q := by
    unfold rc_root
    rw [hq_top]
  have hrL : R^[L] p = rc_root R p := by
    unfold rc_root
    rw [hp]
  have hagree_q : ∀ t : ℕ, t ≤ L →
      (Function.update R x p)^[t] q = R^[t] q :=
    rc_caseC2_qagree R q L hq_top x p hxper
  have hag : (Function.update R x p)^[L - 1] q = R^[L - 1] q :=
    hagree_q (L - 1) (by omega)
  have hclosed : ∀ a : V, ((∃ s' : ℕ, s' < L ∧ R^[s'] p = a) ∨
      (∃ t : ℕ, t ≤ j ∧ R^[t] (rc_root R p) = a)) →
      ((∃ s' : ℕ, s' < L ∧ R^[s'] p = Function.update R x p a) ∨
        (∃ t : ℕ, t ≤ j ∧ R^[t] (rc_root R p) = Function.update R x p a)) := by
    intro a ha
    rcases ha with ⟨s', hs', heq⟩ | ⟨t, ht, heq⟩
    · have hne : R^[s'] p ≠ x := by
        intro hcon
        have hnp : R^[s'] p ∉ Function.periodicPts R :=
          rc_path_point_notMem R p (by omega)
        exact hnp (by rw [hcon]; exact hxper)
      have eR' : Function.update R x p (R^[s'] p) = R (R^[s'] p) :=
        Function.update_of_ne hne _ _
      by_cases hsL : s' + 1 < L
      · refine Or.inl ⟨s' + 1, hsL, ?_⟩
        rw [← heq, eR']
        exact Function.iterate_succ_apply' R s' p
      · refine Or.inr ⟨0, Nat.zero_le j, ?_⟩
        rw [← heq, eR']
        have hsL' : s' + 1 = L := by omega
        have e2 : R (R^[s'] p) = R^[L] p := by
          rw [← hsL']
          exact (Function.iterate_succ_apply' R s' p).symm
        rw [e2, hrL, Function.iterate_zero_apply]
    · by_cases htj : t = j
      · subst htj
        rw [hxj] at heq
        refine Or.inl ⟨0, by omega, ?_⟩
        rw [← heq, Function.iterate_zero_apply, Function.update_self]
      · have hne : R^[t] (rc_root R p) ≠ x := by
          intro hcon
          have htm : t < Function.minimalPeriod R (rc_root R p) := by omega
          exact htj (Function.iterate_injOn_Iio_minimalPeriod htm hjm
            (hcon.trans hxj.symm))
        have eR' : Function.update R x p (R^[t] (rc_root R p)) =
            R (R^[t] (rc_root R p)) := Function.update_of_ne hne _ _
        refine Or.inr ⟨t + 1, by omega, ?_⟩
        rw [← heq, eR']
        exact Function.iterate_succ_apply' R t _
  have hstep : (Function.update R x p)^[1] (R^[L - 1] q) = rc_root R q := by
    rw [rc_update_iterate_one]
    have hne : R^[L - 1] q ≠ x := by
      intro hcon
      exact hnper_q (by rw [hcon]; exact hxper)
    have eR' : Function.update R x p (R^[L - 1] q) = R (R^[L - 1] q) :=
      Function.update_of_ne hne _ _
    have hdec : L = (L - 1) + 1 := by omega
    have e2 : R (R^[L - 1] q) = R^[L] q := by
      conv_rhs => rw [hdec]
      exact (Function.iterate_succ_apply' R (L - 1) q).symm
    rw [eR', e2, hLq]
  have hnper'_q : R^[L - 1] q ∉
      Function.periodicPts (Function.update R x p) := by
    intro hmem
    rw [← hag] at hmem
    have hmemZ : ((∃ s' : ℕ, s' < L ∧ R^[s'] p =
        (Function.update R x p)^[1] ((Function.update R x p)^[L - 1] q)) ∨
        (∃ t : ℕ, t ≤ j ∧ R^[t] (rc_root R p) =
          (Function.update R x p)^[1] ((Function.update R x p)^[L - 1] q))) := by
      rw [hag, hstep]
      exact Or.inr ⟨s, hsj, hsq⟩
    have hZP := rc_mem_of_periodic_iterate_mem _ _ hclosed _ hmem 1 hmemZ
    rcases hZP with ⟨s', hs', heqZ⟩ | ⟨t, ht, heqZ⟩
    · rw [hag] at heqZ
      have e3 : R (R^[s'] p) = R^[s' + 1] p :=
        (Function.iterate_succ_apply' R s' p).symm
      have eL : R^[L] q = R^[s' + 1] p := by
        have e1 : R (R^[L - 1] q) = R (R^[s'] p) := congrArg R heqZ.symm
        have e2 : R (R^[L - 1] q) = R^[L] q := by
          have hdec : L = (L - 1) + 1 := by omega
          conv_rhs => rw [hdec]
          exact (Function.iterate_succ_apply' R (L - 1) q).symm
        rwa [e2, e3] at e1
      have hperL : R^[s' + 1] p ∈ Function.periodicPts R := by
        rw [← eL, hLq]
        exact rc_root_periodic R q
      have hsL' : s' + 1 = L := by
        by_contra hc
        have hlt : s' + 1 < L := by omega
        exact rc_path_point_notMem R p (by omega) hperL
      have hroot_eq : rc_root R q = rc_root R p := by
        have e4 : R^[L] q = R^[L] p := by
          rw [eL, hsL']
        rw [hLq] at e4
        rw [hrL] at e4
        exact e4
      exact hq_root hroot_eq
    · rw [hag] at heqZ
      have hperS : R^[t] (rc_root R p) ∈ Function.periodicPts R :=
        rc_periodic_iterate R hrper t
      rw [heqZ] at hperS
      exact hnper_q hperS
  have hrper' : rc_root R p ∈
      Function.periodicPts (Function.update R x p) := by
    refine Function.mem_periodicPts.mpr ⟨L + j + 1, by omega, ?_⟩
    change (Function.update R x p)^[L + j + 1] (rc_root R p) = rc_root R p
    have e1 : (Function.update R x p)^[L + j + 1] (rc_root R p) =
        (Function.update R x p)^[L] ((Function.update R x p)^[j + 1]
          (rc_root R p)) := by
      have hdec : L + j + 1 = L + (j + 1) := by omega
      conv_lhs => rw [hdec]
      exact Function.iterate_add_apply _ _ _ _
    have e2 : (Function.update R x p)^[j + 1] (rc_root R p) = p :=
      rc_R'_to_p R _ j hjm x p hxj
    have e3 : (Function.update R x p)^[L] p = rc_root R p := by
      rw [rc_R'_agree_tree R p L hp x hxper L le_rfl, hrL]
    rw [e1, e2, e3]
  have hsper : (Function.update R x p)^[s] (rc_root R p) ∈
      Function.periodicPts (Function.update R x p) :=
    rc_periodic_iterate _ hrper' s
  have eag : (Function.update R x p)^[s] (rc_root R p) = R^[s] (rc_root R p) :=
    rc_R'_agree_cycle R _ j hjm x p hxj s hsj
  have hLper : (Function.update R x p)^[L] q ∈
      Function.periodicPts (Function.update R x p) := by
    rw [hagree_q L le_rfl, hLq, ← hsq, ← eag]
    exact hsper
  apply le_antisymm
  · exact rc_level_le_of_mem _ _ hLper
  · by_contra hc
    have hle : rc_level (Function.update R x p) q ≤ L - 1 := by omega
    have hper := rc_iterate_ge_level_periodic _ _ hle
    rw [hag] at hper
    exact hnper'_q hper

private theorem rc_caseC2_gt_false {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (delta : V → Fin k → V) (R : V → V) (hR : rc_isSSG delta R)
    (hHmax : ∀ g : V → V, rc_isSSG delta g → rc_height g ≤ rc_height R)
    (hCmax : ∀ g : V → V, rc_isSSG delta g → rc_height g = rc_height R →
      rc_cyc g ≤ rc_cyc R)
    (L : ℕ) (hL : rc_height R = L) (hH : 1 ≤ L)
    (p : V) (hp : rc_level R p = L)
    (q : V) (hq_top : rc_level R q = L) (hq_root : rc_root R q ≠ rc_root R p)
    (j : ℕ) (hjm : j < Function.minimalPeriod R (rc_root R p))
    (x : V) (hx : rc_adj delta x p) (hxj : R^[j] (rc_root R p) = x)
    (hxper : x ∈ Function.periodicPts R)
    (hC2 : Function.minimalPeriod R (rc_root R p) < L + j + 1) :
    False := by
  classical
  have hR'ssg : rc_isSSG delta (Function.update R x p) :=
    rc_ssg_update_edge delta R hR x p hx
  have hperT : ∀ s : ℕ, s < L →
      R^[s] p ∈ Function.periodicPts (Function.update R x p) :=
    fun s hs => rc_caseC2_tree_per R p L hp j hjm x hxj hxper s hs
  have hperS : ∀ t : ℕ, t ≤ j →
      R^[t] (rc_root R p) ∈ Function.periodicPts (Function.update R x p) :=
    fun t ht => rc_caseC2_seg_per R p L hp j hjm x hxj hxper t ht
  have hcyc : rc_cyc R < rc_cyc (Function.update R x p) :=
    rc_caseC2_cyc R L p hp j hjm x hxj hperT hperS hC2
  have hght : L ≤ rc_height (Function.update R x p) := by
    by_cases hC : rc_root R q ∈ rc_cycleFin R (rc_root R p)
    · obtain ⟨s, hsm, hs⟩ := (rc_cycleFin_mem R _ _).mp hC
      by_cases hsj : s ≤ j
      · have h1 := rc_level_le_height (Function.update R x p) q
        have hlev := rc_caseC2_oncycle_le R p L hp hH j hjm x hxj hxper q
          hq_top hq_root s hsj hs
        omega
      · have hgt' : j < s := by omega
        have hfalse := rc_caseC2_oncycle_gt delta R hR hHmax L hL hH p hp q
          hq_top j hjm x hx hxj hxper s hsm hs hgt'
        exact False.elim hfalse
    · have h1 := rc_level_le_height (Function.update R x p) q
      have hlev := rc_caseC2_offcycle R L p q hq_top j hjm x hxj hxper hC
      omega
  by_cases hgt : L < rc_height (Function.update R x p)
  · have hle := hHmax _ hR'ssg
    omega
  · have heqH : rc_height (Function.update R x p) = rc_height R := by omega
    have hle := hCmax _ hR'ssg heqH
    omega

private theorem rc_inedge_lemma {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (delta : V → Fin k → V) (R : V → V) (hR : rc_isSSG delta R)
    (hHmax : ∀ g : V → V, rc_isSSG delta g → rc_height g ≤ rc_height R)
    (hCmax : ∀ g : V → V, rc_isSSG delta g → rc_height g = rc_height R →
      rc_cyc g ≤ rc_cyc R)
    (hngR : ¬ rc_good R)
    (L : ℕ) (hL : rc_height R = L) (hH : 1 ≤ L)
    (p : V) (hp : rc_level R p = L)
    (x : V) (hx : rc_adj delta x p) :
    x ∈ Function.periodicPts R ∧ R^[L + 1] x = rc_root R p := by
  classical
  have hH' : 1 ≤ rc_height R := by omega
  obtain ⟨q, hq_top, hq_root⟩ := rc_exists_other_top R hH' hngR p
  have hq_topL : rc_level R q = L := by omega
  by_cases horb : ∃ i : ℕ, R^[i] p = x
  · obtain ⟨i, hi⟩ := horb
    by_cases hiL : i < L
    · exfalso
      exact rc_caseB_tree delta R hR hHmax hCmax L hL hH p hp q hq_topL
        hq_root x hx i hi hiL
    · obtain ⟨j, hjm, hxj, hxper⟩ :=
        rc_caseC_setup R p L hp x i hi (by omega)
      rcases lt_trichotomy (L + j + 1)
          (Function.minimalPeriod R (rc_root R p)) with hlt | heq | hgt
      · exfalso
        exact rc_caseC1 delta R hR hHmax L hL hH p hp j hjm x hx hxj hxper hlt
      · refine ⟨hxper, ?_⟩
        have hper_m : R^[Function.minimalPeriod R (rc_root R p)]
            (rc_root R p) = rc_root R p :=
          Function.iterate_minimalPeriod
        have e : R^[L + 1] x = R^[L + 1 + j] (rc_root R p) := by
          rw [← hxj]
          have hdec : L + 1 + j = (L + 1) + j := by omega
          rw [hdec]
          exact (Function.iterate_add_apply R (L + 1) j _).symm
        have heq2 : L + 1 + j = Function.minimalPeriod R (rc_root R p) := by
          omega
        rw [e, heq2, hper_m]
      · exfalso
        exact rc_caseC2_gt_false delta R hR hHmax hCmax L hL hH p hp q
          hq_topL hq_root j hjm x hx hxj hxper hgt
  · exfalso
    have havoid : ∀ i : ℕ, R^[i] p ≠ x := fun i hi => horb ⟨i, hi⟩
    exact rc_caseA_offorbit delta R hR hHmax L hL hH p hp x hx havoid

private theorem rc_bunch_of_lexmax {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (delta : V → Fin k → V)
    (R : V → V) (hR : rc_isSSG delta R)
    (hHmax : ∀ g : V → V, rc_isSSG delta g → rc_height g ≤ rc_height R)
    (hCmax : ∀ g : V → V, rc_isSSG delta g → rc_height g = rc_height R →
      rc_cyc g ≤ rc_cyc R)
    (hnone : ∀ g : V → V, rc_isSSG delta g → ¬ rc_good g)
    (hcon : rc_strongly delta) (hcard : 1 < Fintype.card V)
    (L : ℕ) (hL : rc_height R = L) (hH : 1 ≤ L)
    (p : V) (hp : rc_level R p = L)
    (b : V) (hb : R^[L - 1] p = b) :
    ∀ a : Fin k, delta b a = rc_root R p := by
  classical
  have hH' : 1 ≤ rc_height R := by omega
  have hbnp : b ∉ Function.periodicPts R := by
    rw [← hb]
    exact rc_path_point_notMem R p (by omega)
  have hrootb : rc_root R b = rc_root R p := by
    rw [← hb]
    exact rc_root_along_orbit R p (by omega)
  obtain ⟨q, hq_top, hq_root⟩ := rc_exists_other_top R hH' (hnone R hR) p
  have hq_topL : rc_level R q = L := by omega
  intro a
  by_contra hne
  set v : V := delta b a with hvdef
  have hadj : rc_adj delta b v := ⟨a, hvdef.symm⟩
  have hR'ssg : rc_isSSG delta (Function.update R b v) :=
    rc_ssg_update_edge delta R hR b v hadj
  have hRb' : Function.update R b v b = v := Function.update_self _ _ _
  have hsub : ∀ z : V, z ∈ Function.periodicPts R →
      z ∈ Function.periodicPts (Function.update R b v) := by
    intro z hz
    refine rc_update_periodic R b v z ?_ hz
    intro t heq
    have h1 := rc_periodic_iterate R hz t
    rw [heq] at h1
    exact hbnp h1
  by_cases horb : ∃ i : ℕ, R^[i] v = b
  · obtain ⟨i, hi, hmin⟩ :
      ∃ i : ℕ, R^[i] v = b ∧ ∀ t : ℕ, t < i → R^[t] v ≠ b := by
      refine ⟨Nat.find (p := fun i => R^[i] v = b) horb,
        Nat.find_spec (p := fun i => R^[i] v = b) horb,
        fun t ht => Nat.find_min (p := fun i => R^[i] v = b) horb ht⟩
    have hRi : (Function.update R b v)^[i] v = b := by
      have e := rc_update_agree_upto R b v v i (fun s hs => hmin s hs) i le_rfl
      rw [e]
      exact hi
    have hstep : (Function.update R b v)^[i + 1] v = v := by
      have e : (Function.update R b v)^[i + 1] v =
          Function.update R b v ((Function.update R b v)^[i] v) := by
        rw [show i + 1 = i.succ from rfl]
        exact Function.iterate_succ_apply' _ i v
      rw [e, hRi, hRb']
    have hvper' : v ∈ Function.periodicPts (Function.update R b v) :=
      Function.mem_periodicPts.mpr ⟨i + 1, by omega, hstep⟩
    have hbper' : b ∈ Function.periodicPts (Function.update R b v) := by
      have e1 : (Function.update R b v)^[i + 1] b =
          (Function.update R b v)^[i + 1] ((Function.update R b v)^[i] v) :=
        congrArg _ hRi.symm
      have f1 : (Function.update R b v)^[(i + 1) + i] v =
          (Function.update R b v)^[i + 1] ((Function.update R b v)^[i] v) :=
        Function.iterate_add_apply _ _ _ _
      have f2 : (Function.update R b v)^[i + (i + 1)] v =
          (Function.update R b v)^[i] ((Function.update R b v)^[i + 1] v) :=
        Function.iterate_add_apply _ _ _ _
      have e2 : (Function.update R b v)^[i + 1]
          ((Function.update R b v)^[i] v) =
          (Function.update R b v)^[i] ((Function.update R b v)^[i + 1] v) := by
        have hdec : (i + 1) + i = i + (i + 1) := by omega
        rw [← f1, hdec]
        exact f2
      have hmem : (Function.update R b v)^[i + 1] b = b := by
        rw [e1, e2, hstep, hRi]
      exact Function.mem_periodicPts.mpr ⟨i + 1, by omega, hmem⟩
    have hneq : rc_root R q ≠ rc_root R b := by
      rw [hrootb]
      exact hq_root
    have havoid_q : ∀ t : ℕ, R^[t] q ≠ b := by
      intro t
      exact rc_orbit_avoid_of_root_ne R q b hbnp hneq t
    have hlevq : rc_level (Function.update R b v) q = L := by
      rw [rc_update_level_eq R b v q havoid_q]
      exact hq_topL
    have hght : L ≤ rc_height (Function.update R b v) := by
      have h1 := rc_level_le_height (Function.update R b v) q
      omega
    have hcyc : rc_cyc R < rc_cyc (Function.update R b v) :=
      rc_cyc_gt_of_subset_ne R _ hsub b hbper' hbnp
    by_cases hgt : L < rc_height (Function.update R b v)
    · have hle := hHmax _ hR'ssg
      omega
    · have heqH : rc_height (Function.update R b v) = rc_height R := by omega
      have hle := hCmax _ hR'ssg heqH
      omega
  · have havoid : ∀ i : ℕ, R^[i] v ≠ b := fun i hi => horb ⟨i, hi⟩
    have hagree_v : ∀ s : ℕ, (Function.update R b v)^[s] v = R^[s] v :=
      fun s => rc_update_iterate_agree R b v v havoid s
    have hagree_p : ∀ s : ℕ, s ≤ L - 1 →
        (Function.update R b v)^[s] p = R^[s] p := by
      apply rc_update_agree_upto R b v p (L - 1) _
      intro s hs heq
      rw [← hb] at heq
      exact rc_path_ne_of_lt R p L hp (by omega) (by omega) (by omega) heq
    have hLm1 : (Function.update R b v)^[L - 1] p = b := by
      rw [hagree_p (L - 1) le_rfl]
      exact hb
    have hLp : (Function.update R b v)^[L] p = v := by
      have hdec : L = (L - 1) + 1 := by omega
      have e : (Function.update R b v)^[L] p =
          Function.update R b v ((Function.update R b v)^[L - 1] p) := by
        conv_lhs => rw [hdec]
        rw [show (L - 1) + 1 = ((L - 1)).succ from rfl]
        exact Function.iterate_succ_apply' _ _ _
      rw [e, hLm1, hRb']
    by_cases hvper : v ∈ Function.periodicPts R
    · have hbper'_no : b ∉ Function.periodicPts (Function.update R b v) := by
        intro hmem
        obtain ⟨N, hNpos, hN⟩ := Function.mem_periodicPts.mp hmem
        have hNb : (Function.update R b v)^[N] b = R^[N - 1] v := by
          have hdec : N = (N - 1) + 1 := by omega
          have e : (Function.update R b v)^[N] b =
              (Function.update R b v)^[N - 1] ((Function.update R b v) b) := by
            conv_lhs => rw [hdec]
            rw [Function.iterate_add_apply, rc_update_iterate_one]
          rw [e, hRb']
          exact hagree_v (N - 1)
        have hperNv : R^[N - 1] v ∈ Function.periodicPts R :=
          rc_periodic_iterate R hvper (N - 1)
        have hNb_eq : (Function.update R b v)^[N] b = b := hN
        rw [← hNb] at hperNv
        rw [hNb_eq] at hperNv
        exact hbnp hperNv
      have hvper' : v ∈ Function.periodicPts (Function.update R b v) :=
        rc_update_periodic R b v v havoid hvper
      have hlevp : rc_level (Function.update R b v) p = L := by
        apply le_antisymm
        · exact rc_level_le_of_mem _ _ (by rwa [hLp])
        · by_contra hc
          have hle : rc_level (Function.update R b v) p ≤ L - 1 := by omega
          have hper := rc_iterate_ge_level_periodic _ _ hle
          rw [hLm1] at hper
          exact hbper'_no hper
      have hrootp' : rc_root (Function.update R b v) p = v := by
        unfold rc_root
        rw [hlevp]
        exact hLp
      have hcyc_le : rc_cyc R ≤ rc_cyc (Function.update R b v) := by
        unfold rc_cyc
        apply Finset.card_le_card
        intro z hz
        have hzP : z ∈ Function.periodicPts R := (Finset.mem_filter.mp hz).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, hsub z hzP⟩
      have hght : L ≤ rc_height (Function.update R b v) := by
        have h1 := rc_level_le_height (Function.update R b v) p
        omega
      by_cases hgt2 : L < rc_height (Function.update R b v)
      · have hle := hHmax _ hR'ssg
        omega
      · have heqH : rc_height (Function.update R b v) = L := by omega
        have hHmax' : ∀ g : V → V, rc_isSSG delta g →
            rc_height g ≤ rc_height (Function.update R b v) := by
          intro g hg
          have hle := hHmax g hg
          omega
        have hCmax' : ∀ g : V → V, rc_isSSG delta g →
            rc_height g = rc_height (Function.update R b v) →
            rc_cyc g ≤ rc_cyc (Function.update R b v) := by
          intro g hg heq
          have h1 : rc_height g = rc_height R := by omega
          have h2 := hCmax g hg h1
          omega
        have hngR' : ¬ rc_good (Function.update R b v) :=
          hnone _ hR'ssg
        obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card hcard p
        have hedge : ∃ x, rc_adj delta x p := by
          have hpath := hcon w p
          induction hpath with
          | refl => exact absurd rfl hw
          | tail _ hab _ => exact ⟨_, hab⟩
        obtain ⟨xx, hxx⟩ := hedge
        obtain ⟨hxper, hBx⟩ := rc_inedge_lemma delta R hR hHmax hCmax
          (hnone R hR) L hL hH p hp xx hxx
        obtain ⟨-, hBx'⟩ := rc_inedge_lemma delta _ hR'ssg hHmax' hCmax'
          hngR' L heqH hH p hlevp xx hxx
        have hag : (Function.update R b v)^[L + 1] xx = R^[L + 1] xx := by
          apply rc_update_iterate_agree R b v xx _
          intro t heq
          have h1 := rc_periodic_iterate R hxper t
          rw [heq] at h1
          exact hbnp h1
        rw [hrootp'] at hBx'
        rw [hag, hBx] at hBx'
        have hvv : v = rc_root R p := hBx'.symm
        rw [hvdef] at hne
        exact hne hvv
    · have hnper' : (Function.update R b v)^[L] p ∉
          Function.periodicPts (Function.update R b v) := by
        intro hmem
        rw [hLp] at hmem
        exact hvper (rc_update_periodic_of R b v v hagree_v hmem)
      have hgt : L < rc_height (Function.update R b v) :=
        rc_height_gt_of_iterate_notMem _ p L hnper'
      have hle := hHmax _ hR'ssg
      omega

private theorem rc_B3_height {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V) (p q : V) (L : ℕ) (hp : rc_level R p = L)
    (hq_top : rc_level R q = L) (hq_root : rc_root R q ≠ rc_root R p)
    (hH : 1 ≤ L)
    (r : V) (hr : rc_root R p = r) (hrper : r ∈ Function.periodicPts R)
    (m : ℕ) (hm : m = Function.minimalPeriod R r) (hmpos : 0 < m)
    (c u : V) (hc : R^[m - 1] r = c) (hcP : c ∈ Function.periodicPts R)
    (hrper' : r ∈ Function.periodicPts (Function.update R c u)) :
    L ≤ rc_height (Function.update R c u) := by
  classical
  have hLp : R^[L] p = r := by
    have h : rc_root R p = R^[L] p := by
      unfold rc_root
      rw [hp]
    rw [hr] at h
    exact h.symm
  have hLq : R^[L] q = rc_root R q := by
    unfold rc_root
    rw [hq_top]
  have hbnp : R^[L - 1] p ∉ Function.periodicPts R :=
    rc_path_point_notMem R p (by omega)
  have hzq_np : R^[L - 1] q ∉ Function.periodicPts R :=
    rc_path_point_notMem R q (by omega)
  have hag_p : (Function.update R c u)^[L - 1] p = R^[L - 1] p :=
    rc_update_agree_upto R c u p (L - 1) (by
      intro s hs heq
      have hnp : R^[s] p ∉ Function.periodicPts R :=
        rc_path_point_notMem R p (by omega)
      exact hnp (by rw [heq]; exact hcP)) (L - 1) le_rfl
  have hag_q : (Function.update R c u)^[L - 1] q = R^[L - 1] q :=
    rc_update_agree_upto R c u q (L - 1) (by
      intro s hs heq
      have hnp : R^[s] q ∉ Function.periodicPts R :=
        rc_path_point_notMem R q (by omega)
      exact hnp (by rw [heq]; exact hcP)) (L - 1) le_rfl
  by_cases hboth : (Function.update R c u)^[L - 1] p ∈
      Function.periodicPts (Function.update R c u) ∧
      (Function.update R c u)^[L - 1] q ∈
        Function.periodicPts (Function.update R c u)
  · exfalso
    obtain ⟨hbb, hqq⟩ := hboth
    rw [hag_p] at hbb
    rw [hag_q] at hqq
    have hA : rc_root R u = r := by
      have hRb : (Function.update R c u) (R^[L - 1] p) = r := by
        have hne : R^[L - 1] p ≠ c := by
          intro hcon
          have hmem : R^[L - 1] p ∈ Function.periodicPts R := by
            rw [hcon]
            exact hcP
          exact hbnp hmem
        have eR' : Function.update R c u (R^[L - 1] p) = R (R^[L - 1] p) :=
          Function.update_of_ne hne _ _
        have e2 : R (R^[L - 1] p) = R^[L] p := by
          have hdec : L = (L - 1) + 1 := by omega
          conv_rhs => rw [hdec]
          exact (Function.iterate_succ_apply' R (L - 1) p).symm
        rw [eR', e2, hLp]
      obtain ⟨Nb, hNbpos, hNb⟩ := Function.mem_periodicPts.mp hbb
      have hNb_eq : (Function.update R c u)^[Nb] (R^[L - 1] p) =
          R^[L - 1] p := hNb
      have e_orb : (Function.update R c u)^[Nb - 1] r = R^[L - 1] p := by
        have hdec : Nb = (Nb - 1) + 1 := by omega
        have e : (Function.update R c u)^[Nb] (R^[L - 1] p) =
            (Function.update R c u)^[Nb - 1]
              ((Function.update R c u) (R^[L - 1] p)) := by
          conv_lhs => rw [hdec]
          rw [Function.iterate_add_apply, rc_update_iterate_one]
        rw [hRb] at e
        rw [hNb_eq] at e
        exact e.symm
      obtain ⟨s, hs⟩ := rc_B3_reduce R r hrper m hm hmpos c u hc hcP
        hrper' _ hbnp ⟨Nb - 1, e_orb⟩
      have hsL : s ≤ rc_level R u := by
        by_contra hcon
        have hle : rc_level R u ≤ s := by omega
        have hper := rc_iterate_ge_level_periodic R u hle
        rw [hs] at hper
        exact hbnp hper
      have e2 := rc_root_along_orbit R u hsL
      rw [hs] at e2
      have hrb : rc_root R (R^[L - 1] p) = r := by
        have e3 := rc_root_along_orbit R p (by omega : L - 1 ≤ rc_level R p)
        rw [hr] at e3
        exact e3
      rw [hrb] at e2
      exact e2.symm
    have hB : rc_root R u = rc_root R q := by
      have hRzq : R (R^[L - 1] q) = rc_root R q := by
        have e2 : R (R^[L - 1] q) = R^[L] q := by
          have hdec : L = (L - 1) + 1 := by omega
          conv_rhs => rw [hdec]
          exact (Function.iterate_succ_apply' R (L - 1) q).symm
        rw [e2, hLq]
      have hR'zq : (Function.update R c u) (R^[L - 1] q) = rc_root R q := by
        have hne : R^[L - 1] q ≠ c := by
          intro hcon
          have hmem : R^[L - 1] q ∈ Function.periodicPts R := by
            rw [hcon]
            exact hcP
          exact hzq_np hmem
        have eR' : Function.update R c u (R^[L - 1] q) = R (R^[L - 1] q) :=
          Function.update_of_ne hne _ _
        rw [eR', hRzq]
      obtain ⟨Nq, hNqpos, hNq⟩ := Function.mem_periodicPts.mp hqq
      have hNq_eq : (Function.update R c u)^[Nq] (R^[L - 1] q) =
          R^[L - 1] q := hNq
      have hrootq_per' : rc_root R q ∈
          Function.periodicPts (Function.update R c u) := by
        have hmem : (Function.update R c u)^[Nq] (rc_root R q) =
            rc_root R q := by
          have f1 := Function.iterate_add_apply (Function.update R c u)
            Nq 1 (R^[L - 1] q)
          have f2 := Function.iterate_add_apply (Function.update R c u)
            1 Nq (R^[L - 1] q)
          rw [Nat.add_comm 1 Nq] at f2
          rw [rc_update_iterate_one] at f1 f2
          rw [hR'zq] at f1
          rw [hNq_eq] at f2
          rw [hR'zq] at f2
          rw [f1] at f2
          exact f2
        exact Function.mem_periodicPts.mpr ⟨Nq, hNqpos, hmem⟩
      by_cases hhit : ∃ i : ℕ, R^[i] (R^[L - 1] q) = c
      · obtain ⟨iq, hiq, hminq⟩ :
          ∃ iq : ℕ, R^[iq] (R^[L - 1] q) = c ∧
            ∀ t' : ℕ, t' < iq → R^[t'] (R^[L - 1] q) ≠ c := by
          have hex : ∃ iq : ℕ, R^[iq] (R^[L - 1] q) = c := hhit
          refine ⟨Nat.find (p := fun iq => R^[iq] (R^[L - 1] q) = c) hex,
            Nat.find_spec (p := fun iq => R^[iq] (R^[L - 1] q) = c) hex,
            fun t' ht' =>
              Nat.find_min (p := fun iq => R^[iq] (R^[L - 1] q) = c) hex
                ht'⟩
        have hiqR' : (Function.update R c u)^[iq] (R^[L - 1] q) = c := by
          have eag := rc_update_agree_upto R c u (R^[L - 1] q) iq
            (fun s hs => hminq s hs) iq le_rfl
          rwa [eag]
        have hiqmod : (Function.update R c u)^[iq % Nq] (R^[L - 1] q) = c := by
          have hdec : iq = Nq * (iq / Nq) + iq % Nq := by
            have := Nat.mod_add_div iq Nq
            omega
          have e : (Function.update R c u)^[iq] (R^[L - 1] q) =
              (Function.update R c u)^[Nq * (iq / Nq)]
                ((Function.update R c u)^[iq % Nq] (R^[L - 1] q)) := by
            conv_lhs => rw [hdec]
            exact Function.iterate_add_apply _ _ _ _
          have hpow : (Function.update R c u)^[Nq * (iq / Nq)]
              (R^[L - 1] q) = R^[L - 1] q :=
            hNq.mul_const (iq / Nq)
          have e2 : (Function.update R c u)^[Nq * (iq / Nq)]
              ((Function.update R c u)^[iq % Nq] (R^[L - 1] q)) =
              (Function.update R c u)^[iq % Nq] (R^[L - 1] q) := by
            have f1 := Function.iterate_add_apply (Function.update R c u)
              (Nq * (iq / Nq)) (iq % Nq) (R^[L - 1] q)
            have f2 := Function.iterate_add_apply (Function.update R c u)
              (iq % Nq) (Nq * (iq / Nq)) (R^[L - 1] q)
            rw [Nat.add_comm (iq % Nq) (Nq * (iq / Nq))] at f2
            rw [f1] at f2
            rw [hpow] at f2
            exact f2
          rw [e2] at e
          rw [hiqR'] at e
          exact e.symm
        have hzc : (Function.update R c u)^[Nq - iq % Nq] c =
            R^[L - 1] q := by
          have hdec : Nq = (Nq - iq % Nq) + iq % Nq := by
            have hlt : iq % Nq < Nq := Nat.mod_lt _ hNqpos
            omega
          have e : (Function.update R c u)^[Nq] (R^[L - 1] q) =
              (Function.update R c u)^[Nq - iq % Nq]
                ((Function.update R c u)^[iq % Nq] (R^[L - 1] q)) := by
            conv_lhs => rw [hdec]
            exact Function.iterate_add_apply _ _ _ _
          rw [hiqmod] at e
          rw [hNq_eq] at e
          exact e.symm
        have hcr : (Function.update R c u)^[m - 1] r = c := by
          have eag := rc_R'_agree_cycle R r (m - 1) (by omega) c u hc
            (m - 1) le_rfl
          rwa [hc] at eag
        have hzr : (Function.update R c u)^[Nq - iq % Nq + (m - 1)] r =
            R^[L - 1] q := by
          have e : (Function.update R c u)^[Nq - iq % Nq + (m - 1)] r =
              (Function.update R c u)^[Nq - iq % Nq]
                ((Function.update R c u)^[m - 1] r) :=
            Function.iterate_add_apply _ _ _ _
          rw [e, hcr]
          exact hzc
        obtain ⟨s, hs⟩ := rc_B3_reduce R r hrper m hm hmpos c u hc hcP
          hrper' _ hzq_np ⟨Nq - iq % Nq + (m - 1), hzr⟩
        have hsL : s ≤ rc_level R u := by
          by_contra hcon
          have hle : rc_level R u ≤ s := by omega
          have hper := rc_iterate_ge_level_periodic R u hle
          rw [hs] at hper
          exact hzq_np hper
        have e2 := rc_root_along_orbit R u hsL
        rw [hs] at e2
        have hrb : rc_root R (R^[L - 1] q) = rc_root R q := by
          have e3 := rc_root_along_orbit R q (by omega : L - 1 ≤ rc_level R q)
          exact e3
        rw [hrb] at e2
        exact e2.symm
      · exfalso
        exact hzq_np (rc_update_periodic_of R c u _ (by
          intro j
          exact rc_update_iterate_agree R c u (R^[L - 1] q)
            (fun i hi => hhit ⟨i, hi⟩) j) hqq)
    have hcontra : rc_root R q = rc_root R p := by
      have e1 : rc_root R p = rc_root R u := hr.trans hA.symm
      exact (e1.trans hB).symm
    exact hq_root hcontra
  · have hnb : (Function.update R c u)^[L - 1] p ∉
        Function.periodicPts (Function.update R c u) ∨
        (Function.update R c u)^[L - 1] q ∉
          Function.periodicPts (Function.update R c u) := by
      by_contra hcon
      have h1 : (Function.update R c u)^[L - 1] p ∈
          Function.periodicPts (Function.update R c u) := by
        by_contra hcon1
        exact hcon (Or.inl hcon1)
      have h2 : (Function.update R c u)^[L - 1] q ∈
          Function.periodicPts (Function.update R c u) := by
        by_contra hcon2
        exact hcon (Or.inr hcon2)
      exact hboth ⟨h1, h2⟩
    rcases hnb with hn | hn
    · have hlev : L ≤ rc_level (Function.update R c u) p := by
        by_contra hcon
        have hle : rc_level (Function.update R c u) p ≤ L - 1 := by omega
        have hper := rc_iterate_ge_level_periodic _ _ hle
        exact hn hper
      exact le_trans hlev (rc_level_le_height _ _)
    · have hlev : L ≤ rc_level (Function.update R c u) q := by
        by_contra hcon
        have hle : rc_level (Function.update R c u) q ≤ L - 1 := by omega
        have hper := rc_iterate_ge_level_periodic _ _ hle
        exact hn hper
      exact le_trans hlev (rc_level_le_height _ _)

private theorem rc_B3_false {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (delta : V → Fin k → V)
    (R : V → V) (hR : rc_isSSG delta R)
    (hHmax : ∀ g : V → V, rc_isSSG delta g → rc_height g ≤ rc_height R)
    (hCmax : ∀ g : V → V, rc_isSSG delta g → rc_height g = rc_height R →
      rc_cyc g ≤ rc_cyc R)
    (hnone : ∀ g : V → V, rc_isSSG delta g → ¬ rc_good g)
    (hcon : rc_strongly delta) (hcard : 1 < Fintype.card V)
    (L : ℕ) (hL : rc_height R = L) (hH : 1 ≤ L)
    (p : V) (hp : rc_level R p = L)
    (hno2 : ∀ z x y : V, rc_isBunch delta x z → rc_isBunch delta y z → x = y) :
    False := by
  classical
  have hH' : 1 ≤ rc_height R := by omega
  have hrper0 : rc_root R p ∈ Function.periodicPts R := rc_root_periodic R p
  set m : ℕ := Function.minimalPeriod R (rc_root R p) with hmdef
  have hmpos : 0 < m := by
    rw [hmdef]
    exact Function.minimalPeriod_pos_of_mem_periodicPts hrper0
  set c : V := R^[m - 1] (rc_root R p) with hcdef
  have hcP : c ∈ Function.periodicPts R := by
    rw [hcdef]
    exact rc_periodic_iterate R hrper0 (m - 1)
  have hRc : R c = rc_root R p :=
    rc_B3_Rc R _ hrper0 m hmdef c hcdef.symm
  have hcb : c ≠ R^[L - 1] p := by
    intro hcon
    have hnp : R^[L - 1] p ∉ Function.periodicPts R :=
      rc_path_point_notMem R p (by omega)
    have hmem : R^[L - 1] p ∈ Function.periodicPts R := by
      rw [← hcon]
      exact hcP
    exact hnp hmem
  have hbunch : rc_isBunch delta (R^[L - 1] p) (rc_root R p) :=
    rc_bunch_of_lexmax delta R hR hHmax hCmax hnone hcon hcard
      L hL hH p hp _ rfl
  have hcbunch : ¬ rc_isBunch delta c (rc_root R p) := by
    intro hc2
    exact hcb (hno2 _ c _ hc2 hbunch)
  have hex : ∃ a : Fin k, delta c a ≠ rc_root R p := by
    by_contra hc2
    have hb : rc_isBunch delta c (rc_root R p) := by
      intro a
      by_contra ha
      exact hc2 ⟨a, ha⟩
    exact hcbunch hb
  obtain ⟨aa, haa⟩ := hex
  set u : V := delta c aa with hudef
  have hu : u ≠ rc_root R p := haa
  have hR'ssg : rc_isSSG delta (Function.update R c u) :=
    rc_ssg_update_edge delta R hR c u ⟨aa, hudef.symm⟩
  have hag_p : (Function.update R c u)^[L] p = rc_root R p := by
    have eag : (Function.update R c u)^[L] p = R^[L] p :=
      rc_update_agree_upto R c u p L (by
        intro s hs heq
        have hnp : R^[s] p ∉ Function.periodicPts R :=
          rc_path_point_notMem R p (by omega)
        exact hnp (by rw [heq]; exact hcP)) L le_rfl
    rw [eag]
    unfold rc_root
    rw [hp]
  by_cases hrper' : rc_root R p ∈
      Function.periodicPts (Function.update R c u)
  · have hsub : ∀ z : V, z ∈ Function.periodicPts R →
        z ∈ Function.periodicPts (Function.update R c u) :=
      rc_B3_Psub R _ hrper0 m hmdef c u hcdef.symm hrper'
    have hcyc : rc_cyc R < rc_cyc (Function.update R c u) := by
      by_cases heq : Function.periodicPts (Function.update R c u) =
          Function.periodicPts R
      · exfalso
        exact rc_B3_cyc_strict R c u _ hRc hcP hu hsub heq
      · have hss : Finset.univ.filter (fun v => v ∈ Function.periodicPts R) ⊂
            Finset.univ.filter (fun v =>
              v ∈ Function.periodicPts (Function.update R c u)) := by
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨?_, ?_⟩
          · intro z hz
            have hzP : z ∈ Function.periodicPts R :=
              (Finset.mem_filter.mp hz).2
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, hsub z hzP⟩
          · intro hcon
            apply heq
            have hcoe : (Finset.univ.filter (fun v =>
                v ∈ Function.periodicPts (Function.update R c u)) : Set V) =
                (Finset.univ.filter
                  (fun v => v ∈ Function.periodicPts R) : Set V) :=
              congrArg _ hcon.symm
            rw [Finset.coe_filter, Finset.coe_filter] at hcoe
            simpa using hcoe
        have hcardlt := Finset.card_lt_card hss
        unfold rc_cyc
        exact hcardlt
    obtain ⟨qq, hq_top, hq_root⟩ := rc_exists_other_top R hH' (hnone R hR) p
    have hq_topL : rc_level R qq = L := by omega
    have hght : L ≤ rc_height (Function.update R c u) :=
      rc_B3_height R p qq L hp hq_topL hq_root hH _ rfl hrper0 m hmdef
        hmpos c u hcdef.symm hcP hrper'
    by_cases hgt : L < rc_height (Function.update R c u)
    · have hle := hHmax _ hR'ssg
      omega
    · have heqH : rc_height (Function.update R c u) = rc_height R := by omega
      have hle := hCmax _ hR'ssg heqH
      omega
  · have hnper' : (Function.update R c u)^[L] p ∉
        Function.periodicPts (Function.update R c u) := by
      rwa [hag_p]
    have hgt : L < rc_height (Function.update R c u) :=
      rc_height_gt_of_iterate_notMem _ p L hnper'
    have hle := hHmax _ hR'ssg
    omega

private theorem rc_exists_good_ssg {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (delta : V → Fin k → V)
    (hcon : rc_strongly delta) (haper : rc_aperiodic delta)
    (hcard : 1 < Fintype.card V)
    (hno2 : ∀ z x y : V, rc_isBunch delta x z → rc_isBunch delta y z → x = y) :
    ∃ g : V → V, (∀ v : V, rc_adj delta v (g v)) ∧ rc_good g := by
  classical
  have hpos : 0 < Fintype.card V := by omega
  have hneV : Nonempty V := Fintype.card_pos_iff.mp hpos
  have hk : 0 < k := by
    by_contra hk0
    have hk0' : k = 0 := by omega
    obtain ⟨v₀⟩ := hneV
    obtain ⟨w₀, hne₀⟩ := Fintype.exists_ne_of_one_lt_card hcard v₀
    have hne : v₀ ≠ w₀ := Ne.symm hne₀
    have hempty : ∀ x y : V, ¬ rc_adj delta x y := by
      intro x y h
      obtain ⟨a, _⟩ := h
      exact Fin.elim0 (hk0' ▸ a)
    have heq : v₀ = w₀ := by
      have h := hcon v₀ w₀
      induction h with
      | refl => rfl
      | tail _ hab _ => exact (hempty _ _ hab).elim
    exact hne heq
  obtain ⟨a₀⟩ : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨R, hR, hHmax⟩ := rc_height_max_exists delta a₀
  obtain ⟨R', hR', hHR', hCmax⟩ :=
    rc_cyc_max_exists delta (rc_height R) R ⟨hR, rfl⟩
  have hHmax' : ∀ g : V → V, rc_isSSG delta g →
      rc_height g ≤ rc_height R' := by
    intro g hg
    have hle := hHmax g hg
    omega
  have hCmax' : ∀ g : V → V, rc_isSSG delta g →
      rc_height g = rc_height R' → rc_cyc g ≤ rc_cyc R' := by
    intro g hg heq
    have heq2 : rc_height g = rc_height R := by omega
    exact hCmax g hg heq2
  have hH : 1 ≤ rc_height R' :=
    rc_lexmax_height_pos delta a₀ hcon haper hcard R' hHmax'
  obtain ⟨p, hp⟩ := @rc_height_attained V _ _ hneV R'
  by_contra hnone
  have hnone' : ∀ g : V → V, rc_isSSG delta g → ¬ rc_good g := by
    intro g hg hgg
    exact hnone ⟨g, hg, hgg⟩
  exact rc_B3_false delta R' hR' hHmax' hCmax' hnone' hcon hcard
    (rc_height R') rfl hH p hp hno2

private theorem rc_exists_stable_recolor {V : Type*} [Fintype V] [Nonempty V]
    {k : ℕ} (delta : V → Fin k → V) (a₀ : Fin k)
    (hcon : rc_strongly delta) (haper : rc_aperiodic delta)
    (hcard : 1 < Fintype.card V) :
    ∃ sigma1 : V → Equiv.Perm (Fin k), ∃ x y : V, x ≠ y ∧
      rc_stable (rc_recolor delta sigma1) x y := by
  classical
  by_cases h2 : ∃ z x y : V, x ≠ y ∧ rc_isBunch delta x z ∧ rc_isBunch delta y z
  · obtain ⟨z, x, y, hne, hxb, hyb⟩ := h2
    exact ⟨fun _ => 1, x, y, hne,
      rc_stable_of_two_bunches _ a₀ (rc_bunch_recolor _ _ hxb)
        (rc_bunch_recolor _ _ hyb)⟩
  · have hno2 : ∀ z x y : V, rc_isBunch delta x z → rc_isBunch delta y z →
      x = y := by
      intro z x y hx hy
      by_contra hne
      exact h2 ⟨z, x, y, hne, hx, hy⟩
    obtain ⟨g, hg_adj, hgood⟩ := rc_exists_good_ssg delta hcon haper hcard hno2
    obtain ⟨sigma1, hsigma1⟩ := rc_recolor_realizes_ssg delta g hg_adj a₀
    have hAcon : rc_strongly (rc_recolor delta sigma1) :=
      (rc_strongly_recolor delta sigma1).mpr hcon
    obtain ⟨L, r, p, hL, _hLeq, _hplev, _hrroot, hper, htop, hcoll⟩ :=
      rc_good_bridge g hgood
    obtain ⟨x, y, hne, hst⟩ := rc_exists_stable_pair_of_good_letter
      (rc_recolor delta sigma1) hAcon a₀ g
      (fun v => (hsigma1 v).symm) L hL r p hper htop hcoll
    exact ⟨sigma1, x, y, hne, hst⟩

private theorem rc_sync_recolor_bounded {k : ℕ} (m : ℕ) :
    ∀ {V : Type*} [Fintype V] [Nonempty V], Fintype.card V ≤ m →
    ∀ (delta : V → Fin k → V), rc_strongly delta → rc_aperiodic delta →
    ∃ sigma : V → Equiv.Perm (Fin k), rc_sync (rc_recolor delta sigma) := by
  induction m with
  | zero =>
    intro V _ _ hcard delta hcon haper
    have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr inferInstance
    omega
  | succ m ih =>
    intro V _ _ hcard delta hcon haper
    classical
    by_cases h1 : Fintype.card V = 1
    · obtain ⟨r, hr⟩ := Fintype.card_eq_one_iff.mp h1
      exact ⟨fun _ => 1, [], r, fun v => hr v⟩
    · have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr inferInstance
      have hlt1 : 1 < Fintype.card V := by omega
      have hk : 0 < k := by
        by_contra hk0
        have hk0' : k = 0 := by omega
        obtain ⟨v₀⟩ : Nonempty V := inferInstance
        obtain ⟨w₀, hne₀⟩ := Fintype.exists_ne_of_one_lt_card hlt1 v₀
        have hne : v₀ ≠ w₀ := Ne.symm hne₀
        have hempty : ∀ x y : V, ¬ rc_adj delta x y := by
          intro x y h
          obtain ⟨a, _⟩ := h
          exact Fin.elim0 (hk0' ▸ a)
        have heq : v₀ = w₀ := by
          have h := hcon v₀ w₀
          induction h with
          | refl => rfl
          | tail _ hab _ => exact (hempty _ _ hab).elim
        exact hne heq
      obtain ⟨sigma1, x, y, hne, hst⟩ :=
        rc_exists_stable_recolor delta ⟨0, hk⟩ hcon haper hlt1
      have hAcon : rc_strongly (rc_recolor delta sigma1) :=
        (rc_strongly_recolor delta sigma1).mpr hcon
      have hAaper : rc_aperiodic (rc_recolor delta sigma1) :=
        (rc_aperiodic_recolor delta sigma1).mpr haper
      have hQlt : Fintype.card
          (Quotient (rc_stableSetoid (rc_recolor delta sigma1))) < Fintype.card V :=
        rc_quot_card_lt _ hne hst
      have hQle : Fintype.card
          (Quotient (rc_stableSetoid (rc_recolor delta sigma1))) ≤ m := by omega
      obtain ⟨sigma', w', r', hw'⟩ := ih hQle (rc_quot (rc_recolor delta sigma1))
        (rc_quot_strongly _ hAcon) (rc_quot_aperiodic _ hAaper)
      obtain ⟨y₀, hy₀⟩ := Quotient.exists_rep r'
      have hpair : ∀ s₁ ∈ Finset.univ.image
            (fun v => List.foldl (rc_recolor (rc_recolor delta sigma1)
              (fun v => sigma' (Quotient.mk _ v))) v w'),
          ∀ s₂ ∈ Finset.univ.image
            (fun v => List.foldl (rc_recolor (rc_recolor delta sigma1)
              (fun v => sigma' (Quotient.mk _ v))) v w'),
          rc_stable (rc_recolor (rc_recolor delta sigma1)
            (fun v => sigma' (Quotient.mk _ v))) s₁ s₂ := by
        intro s₁ hs₁ s₂ hs₂
        obtain ⟨v₁, _, rfl⟩ := Finset.mem_image.mp hs₁
        obtain ⟨v₂, _, rfl⟩ := Finset.mem_image.mp hs₂
        have e1 : Quotient.mk (rc_stableSetoid (rc_recolor delta sigma1))
            (List.foldl (rc_recolor (rc_recolor delta sigma1)
              (fun v => sigma' (Quotient.mk _ v))) v₁ w') = r' := by
          rw [rc_lift_quot_foldl]
          exact hw' _
        have e2 : Quotient.mk (rc_stableSetoid (rc_recolor delta sigma1))
            (List.foldl (rc_recolor (rc_recolor delta sigma1)
              (fun v => sigma' (Quotient.mk _ v))) v₂ w') = r' := by
          rw [rc_lift_quot_foldl]
          exact hw' _
        have hsame : Quotient.mk (rc_stableSetoid (rc_recolor delta sigma1))
            (List.foldl (rc_recolor (rc_recolor delta sigma1)
              (fun v => sigma' (Quotient.mk _ v))) v₁ w') =
            Quotient.mk (rc_stableSetoid (rc_recolor delta sigma1))
            (List.foldl (rc_recolor (rc_recolor delta sigma1)
              (fun v => sigma' (Quotient.mk _ v))) v₂ w') := by
          rw [e1, e2]
        exact rc_stable_lift _ _ (Quotient.exact hsame)
      obtain ⟨vbar, rfin, hfin⟩ :=
        rc_exists_merge_of_pairwise_stable _ _ hpair
      refine ⟨fun v => sigma1 v * sigma' (Quotient.mk _ v), w' ++ vbar, rfin, ?_⟩
      intro v
      rw [← rc_recolor_recolor, List.foldl_append]
      exact hfin _ (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩)

private theorem rc_exists_sync_recolor {k : ℕ} {V : Type*} [Finite V] [Nonempty V]
    (delta : V → Fin k → V) (hcon : rc_strongly delta)
    (haper : rc_aperiodic delta) :
    ∃ sigma : V → Equiv.Perm (Fin k), rc_sync (rc_recolor delta sigma) := by
  classical
  have : Fintype V := Fintype.ofFinite V
  exact rc_sync_recolor_bounded (Fintype.card V) le_rfl delta hcon haper

end RoadColoring

/-- Road coloring theorem, in the form with `[Finite V]` instead of `[Fintype V]`. -/
theorem roadColoring' :
    ∀ {V : Type*} [Finite V] [Nonempty V]
      (Adj : V → V → Prop),
      (∀ u v : V, Relation.ReflTransGen Adj u v) →
      (∀ d : ℕ, 1 < d → ∃ (u : V) (w : List V),
        List.IsChain Adj (u :: w) ∧ w.getLast? = some u ∧ ¬ (d ∣ w.length)) →
      (∃ k : ℕ, 0 < k ∧ ∀ v : V, Nonempty ({ w : V // Adj v w } ≃ Fin k)) →
      ∃ (k : ℕ) (trans : V → Fin k → V),
        (∀ v : V, ∀ c : Fin k, Adj v (trans v c)) ∧
        (∀ v : V, Function.Injective (trans v)) ∧
        (∀ (v w : V), Adj v w → ∃ c : Fin k, trans v c = w) ∧
        ∃ (word : List (Fin k)) (r : V), ∀ v : V, List.foldl trans v word = r := by
  intro V _ _ Adj hcon haper hreg
  obtain ⟨k, hk, he⟩ := hreg
  have e : ∀ v : V, { w : V // Adj v w } ≃ Fin k :=
    fun v => Classical.choice (he v)
  obtain ⟨delta, hadj_mem, hinj, hcov, hadj_eq, hrecol⟩ :=
    RoadColoring.rc_automaton_of_regular Adj k e
  have hcon' : RoadColoring.rc_strongly delta := by
    intro u v
    rw [hadj_eq]
    exact hcon u v
  have haper' : RoadColoring.rc_aperiodic delta := by
    intro d hd
    obtain ⟨u, w, hchain, hlast, hdiv⟩ := haper d hd
    rw [← hadj_eq] at hchain
    exact ⟨u, w, hchain, hlast, hdiv⟩
  obtain ⟨sigma, word, r, hsync⟩ :=
    RoadColoring.rc_exists_sync_recolor delta hcon' haper'
  exact ⟨k, RoadColoring.rc_recolor delta sigma, (hrecol sigma).1,
    (hrecol sigma).2.1, (hrecol sigma).2.2, word, r, hsync⟩
end
end MetaMathlibExt
