import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_CerednikDrinfeld_WalkOverlap
open SimpleGraph
open CerednikDrinfeld.Mumford CerednikDrinfeld


/-- ported from external source -/

private lemma  sigma_eq_one_or
  {V : Type}
  [DecidableEq V]
  {T : SimpleGraph V}
  (hT : T.IsTree) {x y : V} (hxy : T.Adj x y) (t : V) :
  (T.dist t y : ℤ) - T.dist t x = 1 ∨ (T.dist t y : ℤ) - T.dist t x = -1 := by
  rcases hT.dist_eq_dist_add_one_of_adj t hxy with h | h
  ·
    right
    rw [h]
    push_cast
    ring
  ·
    left
    rw [h]
    push_cast
    ring

private lemma  sigma_self_left
  {V : Type}
  [DecidableEq V]
  {T : SimpleGraph V}
  {x y : V} (hxy : T.Adj x y) : (T.dist x y : ℤ) - T.dist x x = 1 := by
  rw [SimpleGraph.dist_self, dist_eq_one_iff_adj.mpr hxy]; norm_num

private lemma  sigma_self_right
  {V : Type}
  [DecidableEq V]
  {T : SimpleGraph V}
  {x y : V} (hxy : T.Adj x y) : (T.dist y y : ℤ) - T.dist y x = -1 := by
  rw [SimpleGraph.dist_self, dist_eq_one_iff_adj.mpr hxy.symm]; norm_num

private lemma  eq_of_sigma_eq
  {V : Type}
  [DecidableEq V]
  {T : SimpleGraph V}
  (hT : T.IsTree) {x y a b : V} (hxy : T.Adj x y) (hab : T.Adj a b)
  (ha : (T.dist a y : ℤ) - T.dist a x = 1) (hb : (T.dist b y : ℤ) - T.dist b x = -1) : a = x ∧ b = y := by
  have hA := hT.isAcyclic
  have hay : T.dist a y = T.dist a x + 1 := by omega
  have hbx : T.dist b x = T.dist b y + 1 := by omega
  have h1 := hT.dist_eq_dist_add_one_of_adj x hab
  have h2 := hT.dist_eq_dist_add_one_of_adj y hab
  rw [SimpleGraph.dist_comm (u := x), SimpleGraph.dist_comm (u := x) (v := b)] at h1
  rw [SimpleGraph.dist_comm (u := y), SimpleGraph.dist_comm (u := y) (v := b)] at h2
  have hn : T.dist b y = T.dist a x := by omega
  set n := T.dist a x with hn_def
  obtain ⟨p, hp, hpl⟩ := hT.connected.exists_path_of_dist a x
  obtain ⟨q, hq, hql⟩ := hT.connected.exists_path_of_dist b y
  obtain ⟨r, hr, hrl⟩ := hT.connected.exists_path_of_dist a y
  have hxr : x ∈ r.support := by
    by_contra hxr
    have hyp : y ∈ p.support := hA.mem_support_of_ne_mem_support_of_adj_of_isPath hp hr hxy hxr
    have := SimpleGraph.dist_le (p.takeUntil y hyp)
    have := p.length_takeUntil_le hyp
    omega
  have hr_eq : r = p.concat hxy := hA.path_concat hp hr hxy hxr
  by_cases haq : a ∈ q.support
  ·
    have := SimpleGraph.dist_le (q.dropUntil a haq)
    have := q.length_dropUntil_le haq
    omega
  have hs : (Walk.cons hab q).IsPath := hq.cons haq
  have hrs : r = Walk.cons hab q := Subtype.mk.inj (hA.path_unique ⟨r, hr⟩ ⟨_, hs⟩)
  have hb_r : b ∈ r.support := by rw [hrs, Walk.support_cons]; apply List.mem_cons_of_mem _ q.start_mem_support
  rw [hr_eq, Walk.support_concat, List.mem_append, List.mem_singleton] at hb_r
  rcases hb_r with hbp | rfl
  ·
    have := SimpleGraph.dist_le (p.dropUntil b hbp)
    have := p.length_dropUntil_le hbp
    omega
  ·
    have h1' : T.dist a b = 1 := dist_eq_one_iff_adj.mpr hab
    have hn0 : n = 0 := by omega
    have hax : a = x := by
      have : T.dist a x = 0 := by rw [← hn_def, hn0]
      exact (hT.connected.dist_eq_zero_iff.mp this)
    refine ⟨hax, rfl⟩

private lemma  sigma_sub_sigma
  {V : Type}
  [DecidableEq V]
  {T : SimpleGraph V}
  (hT : T.IsTree) {x y a b : V} (hxy : T.Adj x y) (hab : T.Adj a b) :
  ((T.dist a y : ℤ) - T.dist a x) - ((T.dist b y : ℤ) - T.dist b x) =
    2 * ((if a = x ∧ b = y then 1 else 0) - (if a = y ∧ b = x then 1 else 0)) := by
  have hne : x ≠ y := hxy.ne
  rcases sigma_eq_one_or hT hxy a with ha | ha <;> rcases sigma_eq_one_or hT hxy b with hb | hb
  ·
    have h1 : ¬ (a = x ∧ b = y) := by
      rintro ⟨rfl, rfl⟩; rw [sigma_self_right hxy] at hb; norm_num at hb
    have h2 : ¬ (a = y ∧ b = x) := by
      rintro ⟨rfl, rfl⟩; rw [sigma_self_right hxy] at ha; norm_num at ha
    rw [ite_eq_right h1, ite_eq_right h2]; omega
  ·
    obtain ⟨rfl, rfl⟩ := eq_of_sigma_eq hT hxy hab ha hb
    rw [ite_eq_left ⟨rfl, rfl⟩, ite_eq_right (fun h => hne h.1)]
    omega
  ·
    obtain ⟨rfl, rfl⟩ := eq_of_sigma_eq hT hxy hab.symm hb ha
    rw [ite_eq_right (fun h => hne h.1.symm), ite_eq_left ⟨rfl, rfl⟩]
    omega
  ·
    have h1 : ¬ (a = x ∧ b = y) := by
      rintro ⟨rfl, rfl⟩; rw [sigma_self_left hxy] at ha; norm_num at ha
    have h2 : ¬ (a = y ∧ b = x) := by
      rintro ⟨rfl, rfl⟩; rw [sigma_self_left hxy] at hb; norm_num at hb
    rw [ite_eq_right h1, ite_eq_right h2]; omega

private lemma  two_mul_count_sub_count
  {V : Type}
  [DecidableEq V]
  {T : SimpleGraph V}
  (hT : T.IsTree) {a b : V} (hab : T.Adj a b) {X Y : V} (Q : T.Walk X Y) :
  2 * (((Q.darts.count ⟨(a, b), hab⟩ : ℕ) : ℤ) - ((Q.darts.count ⟨(b, a), hab.symm⟩ : ℕ) : ℤ)) =
    ((T.dist b X : ℤ) - T.dist b Y) - ((T.dist a X : ℤ) - T.dist a Y) := by
  induction Q with
  | nil => simp
  | @cons X c Y' hXc Q' ih =>
    rw [Walk.darts_cons, List.count_cons, List.count_cons]
    have key := sigma_sub_sigma hT hXc hab
    have e1 : ((if ((⟨(X, c), hXc⟩ : T.Dart) == ⟨(a, b), hab⟩) = true then 1 else 0 : ℕ) : ℤ) =
        if a = X ∧ b = c then 1 else 0 := by
      by_cases h : a = X ∧ b = c
      ·
        obtain ⟨rfl, rfl⟩ := h
        simp
      ·
        rw [ite_eq_right h]
        have hne : ¬ ((⟨(X, c), hXc⟩ : T.Dart) = ⟨(a, b), hab⟩) := by
          intro h'; apply h
          have h1 := congrArg (fun d : T.Dart => d.toProd.1) h'
          have h2 := congrArg (fun d : T.Dart => d.toProd.2) h'
          refine ⟨h1.symm, h2.symm⟩
        simp [hne]
    have e2 : ((if ((⟨(X, c), hXc⟩ : T.Dart) == ⟨(b, a), hab.symm⟩) = true then 1 else 0 : ℕ) : ℤ) =
        if a = c ∧ b = X then 1 else 0 := by
      by_cases h : a = c ∧ b = X
      ·
        obtain ⟨rfl, rfl⟩ := h
        simp
      ·
        rw [ite_eq_right h]
        have hne : ¬ ((⟨(X, c), hXc⟩ : T.Dart) = ⟨(b, a), hab.symm⟩) := by
          intro h'; apply h
          have h1 := congrArg (fun d : T.Dart => d.toProd.1) h'
          have h2 := congrArg (fun d : T.Dart => d.toProd.2) h'
          refine ⟨h2.symm, h1.symm⟩
        simp [hne]
    rw [Nat.cast_add, Nat.cast_add, e1, e2]
    linear_combination ih - key

private lemma helper_main
  {V : Type}
  [DecidableEq V]
  {T : SimpleGraph V}
  (hT : T.IsTree) {Z Z₀ X Y : V} (P : T.Walk Z Z₀) (Q : T.Walk X Y) :
  (T.dist Z Y : ℤ) + T.dist Z₀ X - T.dist Z X - T.dist Z₀ Y = 2 * CerednikDrinfeld.Mumford.walkOverlap P Q := by
  induction P with
  | nil => rw [walkOverlap_nil_left]; ring
  | @cons Z w Z₀' hZw P' ih =>
    rw [walkOverlap_cons_left, mul_add, ← ih]
    have hd := two_mul_count_sub_count hT hZw Q
    rw [show ((⟨(Z, w), hZw⟩ : T.Dart).symm) = ⟨(w, Z), hZw.symm⟩ from rfl, hd]
    ring
@[path]
private lemma main
  [DecidableEq V]
  {T : SimpleGraph V}
  {Z Z₀ X Y : V}
  {P : T.Walk Z Z₀}
  {Q : T.Walk X Y}
-- given
  (hT : T.IsTree) :
-- imply
  (T.dist Z Y : ℤ) + T.dist Z₀ X - T.dist Z X - T.dist Z₀ Y = 2 * CerednikDrinfeld.Mumford.walkOverlap P Q :=
-- proof
  helper_main hT P Q


-- created on 2026-10-23
