import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.RoadColoring
open MetaMathlibExt


namespace MetaMathlibExt.RoadColoring

/--
[rc_adj_recolor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_adj_recolor {V : Type*} {k : ℕ} (delta : V → Fin k → V)
  (sigma : V → Equiv.Perm (Fin k)) :
  rc_adj (rc_recolor delta sigma) = rc_adj delta := by
  funext v w
  apply propext
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨sigma v a, ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨(sigma v).symm a, by simpa [rc_recolor, Equiv.apply_symm_apply] using ha⟩

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_recolor_recolor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_recolor_recolor {V : Type*} {k : ℕ} (delta : V → Fin k → V)
  (sigma tau : V → Equiv.Perm (Fin k)) :
  rc_recolor (rc_recolor delta sigma) tau =
    rc_recolor delta (fun v => sigma v * tau v) := by
  funext v a
  simp [rc_recolor, Equiv.Perm.mul_apply]

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_strongly_recolor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_strongly_recolor {V : Type*} {k : ℕ} (delta : V → Fin k → V)
  (sigma : V → Equiv.Perm (Fin k)) :
  rc_strongly (rc_recolor delta sigma) ↔ rc_strongly delta := by
  unfold rc_strongly
  rw [rc_adj_recolor]

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_aperiodic_recolor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_aperiodic_recolor {V : Type*} {k : ℕ} (delta : V → Fin k → V)
  (sigma : V → Equiv.Perm (Fin k)) :
  rc_aperiodic (rc_recolor delta sigma) ↔ rc_aperiodic delta := by
  unfold rc_aperiodic
  rw [rc_adj_recolor]

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_exists_word_of_reflTransGen](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_exists_word_of_reflTransGen {V : Type*} {k : ℕ}
  (delta : V → Fin k → V)
  {u v : V} (h : Relation.ReflTransGen (rc_adj delta) u v) :
  ∃ w : List (Fin k), List.foldl delta u w = v := by
  induction h with
  | refl => exact ⟨[], rfl⟩
  | tail _ hab ih =>
    obtain ⟨w, hw⟩ := ih
    obtain ⟨a, ha⟩ := hab
    exact ⟨w ++ [a], by rw [List.foldl_append]; simp [hw, ha]⟩

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_recolor_realizes_ssg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_recolor_realizes_ssg {V : Type*} {k : ℕ} (delta : V → Fin k → V)
  (g : V → V) (hg : ∀ v : V, rc_adj delta v (g v)) (a : Fin k) :
  ∃ sigma : V → Equiv.Perm (Fin k),
    ∀ v : V, rc_recolor delta sigma v a = g v := by
  choose c hc using hg
  exact ⟨fun v => Equiv.swap a (c v), fun v => by
    simp [rc_recolor, Equiv.swap_apply_left, hc v]⟩

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_automaton_of_regular](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_automaton_of_regular {V : Type*} (Adj : V → V → Prop) (k : ℕ)
  (e : ∀ v : V, { w : V // Adj v w } ≃ Fin k) :
  ∃ delta : V → Fin k → V,
    (∀ v a, Adj v (delta v a)) ∧
    (∀ v, Function.Injective (delta v)) ∧
    (∀ v w, Adj v w → ∃ a, delta v a = w) ∧
    rc_adj delta = Adj ∧
    ∀ sigma : V → Equiv.Perm (Fin k),
      (∀ v a, Adj v (rc_recolor delta sigma v a)) ∧
      (∀ v, Function.Injective (rc_recolor delta sigma v)) ∧
      (∀ v w, Adj v w → ∃ a, rc_recolor delta sigma v a = w) := by
  refine ⟨fun v a => ((e v).symm a).val, fun v a => ((e v).symm a).property, ?_, ?_, ?_, ?_⟩
  · intro v a b hab
    have h : (e v).symm a = (e v).symm b := Subtype.ext hab
    exact (e v).symm.injective h
  · intro v w hw
    exact ⟨e v ⟨w, hw⟩, by simp⟩
  · funext v w
    apply propext
    constructor
    · rintro ⟨a, rfl⟩
      exact ((e v).symm a).property
    · intro hw
      exact ⟨e v ⟨w, hw⟩, by simp⟩
  · intro sigma
    refine ⟨fun v a => ((e v).symm (sigma v a)).property, ?_, ?_⟩
    · intro v a b hab
      have h : (e v).symm (sigma v a) = (e v).symm (sigma v b) := Subtype.ext hab
      have h2 := (e v).symm.injective h
      exact (sigma v).injective h2
    · intro v w hw
      refine ⟨(sigma v).symm (e v ⟨w, hw⟩), ?_⟩
      change ((e v).symm (sigma v ((sigma v).symm (e v ⟨w, hw⟩)))).val = w
      rw [Equiv.apply_symm_apply]
      exact congrArg Subtype.val (Equiv.symm_apply_apply (e v) ⟨w, hw⟩)

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_stable_merge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_stable_merge {V : Type*} {k : ℕ} (delta : V → Fin k → V)
  {p q : V} (h : rc_stable delta p q) :
  ∃ v : List (Fin k),
    List.foldl delta p v = List.foldl delta q v := by
  obtain ⟨v, hv⟩ := h []
  exact ⟨v, by simpa using hv⟩

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_exists_branching](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_exists_branching {V : Type*} [Fintype V] {k : ℕ}
  (delta : V → Fin k → V) (hcard : 1 < Fintype.card V)
  (hcon : rc_strongly delta) (haper : rc_aperiodic delta) :
  ∃ v a b, delta v a ≠ delta v b := by
  by_contra hncon
  have hno : ∀ v (a b : Fin k), delta v a = delta v b :=
    fun v a b => of_not_not (fun h => hncon ⟨v, a, b, h⟩)
  have hneV : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨u₀⟩ := hneV
  obtain ⟨w₀, hne₀⟩ := Fintype.exists_ne_of_one_lt_card hcard u₀
  have hne : u₀ ≠ w₀ := Ne.symm hne₀
  have hk : 0 < k := by
    by_contra hkpos
    have hk0 : k = 0 := by omega
    have hempty : ∀ x y : V, ¬ rc_adj delta x y := by
      intro x y h
      obtain ⟨a, _⟩ := h
      exact Fin.elim0 (hk0 ▸ a)
    have huw : u₀ = w₀ := by
      have h := hcon u₀ w₀
      induction h with
      | refl => rfl
      | tail _ hab _ => exact (hempty _ _ hab).elim
    exact hne huw
  classical
  have a₀ : Fin k := ⟨0, hk⟩
  set g : V → V := fun v => delta v a₀ with hg
  have hgraph : ∀ v w : V, rc_adj delta v w ↔ g v = w := by
    intro v w
    constructor
    · rintro ⟨a, ha⟩
      exact (hno v a a₀).symm.trans ha
    · intro h
      exact ⟨a₀, h⟩
  have hit : ∀ u w : V, ∃ i : ℕ, g^[i] u = w := by
    intro u w
    have h := hcon u w
    induction h with
    | refl => exact ⟨0, rfl⟩
    | tail _ hab ih =>
      obtain ⟨i, hi⟩ := ih
      obtain ⟨a, ha⟩ := hab
      refine ⟨i + 1, ?_⟩
      rw [show i + 1 = i.succ from rfl, Function.iterate_succ_apply']
      rw [hi]
      exact (hno _ a₀ a).trans ha
  have hsurj : Function.Surjective g := by
    intro w
    have hne_w : ∃ u : V, u ≠ w := by
      by_contra hcon
      have hall : ∀ u : V, u = w := fun u => of_not_not (fun hne => hcon ⟨u, hne⟩)
      have hle : Fintype.card V ≤ 1 :=
        Fintype.card_le_one_iff.mpr (fun a b => (hall a).trans (hall b).symm)
      omega
    obtain ⟨u, huw⟩ := hne_w
    obtain ⟨i, hi⟩ := hit u w
    cases i with
    | zero =>
      have huv : u = w := hi
      exact absurd huv huw
    | succ j =>
      rw [Function.iterate_succ_apply'] at hi
      exact ⟨g^[j] u, hi⟩
  have hinj : Function.Injective g := Finite.injective_iff_surjective.mpr hsurj
  have hgen : ∀ (w : List V) (u last : V), List.IsChain (rc_adj delta) (u :: w) →
    w.getLast? = some last → g^[w.length] u = last := by
    intro w
    induction w with
    | nil => intro u last _ hlast; simp at hlast
    | cons x xs ih =>
      intro u last hchain hlast
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hhead, htail⟩ := hchain
      have hux : g u = x := (hgraph u x).mp hhead
      cases xs with
      | nil =>
        cases hlast
        have hlen : ([x]).length = 1 := rfl
        rwa [hlen, Function.iterate_one]
      | cons y ys =>
        rw [List.getLast?_cons_cons] at hlast
        have hih := ih x last htail hlast
        have hlen : (x :: y :: ys).length = (y :: ys).length + 1 := rfl
        rwa [hlen, Function.iterate_succ_apply, hux]
  have hper_eq : ∀ x : V, Function.minimalPeriod g x = Fintype.card V := by
    intro x
    have hxper : x ∈ Function.periodicPts g := hinj.mem_periodicPts x
    have hnpos : 0 < Function.minimalPeriod g x :=
      Function.minimalPeriod_pos_of_mem_periodicPts hxper
    have hsurj' : Function.Surjective
      (fun i : Fin (Function.minimalPeriod g x) => g^[i.val] x) := by
      intro w
      obtain ⟨i, hi⟩ := hit x w
      have hpern : g^[(Function.minimalPeriod g x) * (i / Function.minimalPeriod g x)] x = x :=
        Function.isPeriodicPt_iff_minimalPeriod_dvd.mpr (Nat.dvd_mul_right _ _)
      have hdecomp : i % Function.minimalPeriod g x +
        Function.minimalPeriod g x * (i / Function.minimalPeriod g x) = i :=
        Nat.mod_add_div i _
      have hi2 : g^[i % Function.minimalPeriod g x +
        Function.minimalPeriod g x * (i / Function.minimalPeriod g x)] x = w := by
        rwa [hdecomp]
      rw [Function.iterate_add_apply, hpern] at hi2
      exact ⟨⟨i % Function.minimalPeriod g x, Nat.mod_lt i hnpos⟩, hi2⟩
    have hfin : Fintype.card V ≤
      Fintype.card (Fin (Function.minimalPeriod g x)) :=
      Fintype.card_le_of_surjective _ hsurj'
    rw [Fintype.card_fin] at hfin
    exact Nat.le_antisymm (Function.minimalPeriod_le_card (f := g) (x := x)) hfin
  obtain ⟨u, w, hchain, hlast, hdiv⟩ := haper _ hcard
  have hfix : g^[w.length] u = u := hgen w u u hchain hlast
  have hdvd : Fintype.card V ∣ w.length := by
    have h := Function.IsPeriodicPt.minimalPeriod_dvd hfix
    rwa [hper_eq u] at h
  exact hdiv hdvd

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_minRank_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_minRank_le {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
  (delta : V → Fin k → V) (w : List (Fin k)) :
  rc_minRank delta ≤ (Finset.univ.image (fun v => List.foldl delta v w)).card := by
  classical
  exact Nat.find_min' (p := fun n => ∃ w : List (Fin k),
    (Finset.univ.image (fun v => List.foldl delta v w)).card = n) _ ⟨w, rfl⟩

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_minRank_attained](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_minRank_attained {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
  (delta : V → Fin k → V) :
  ∃ w : List (Fin k),
    (Finset.univ.image (fun v => List.foldl delta v w)).card = rc_minRank delta := by
  classical
  exact Nat.find_spec (p := fun n => ∃ w : List (Fin k),
    (Finset.univ.image (fun v => List.foldl delta v w)).card = n) _

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_image_append](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_image_append {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
  (delta : V → Fin k → V) (w u : List (Fin k)) :
  (Finset.univ.image (fun v => List.foldl delta v w)).image
    (fun x => List.foldl delta x u) =
    Finset.univ.image (fun v => List.foldl delta v (w ++ u)) := by
  classical
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, ⟨v, h1⟩, h2⟩
    exact ⟨v, by rw [List.foldl_append, h1]; exact h2⟩
  · rintro ⟨v, h⟩
    refine ⟨List.foldl delta v w, ⟨v, rfl⟩, ?_⟩
    rwa [← List.foldl_append]

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_injOn_of_minRank](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_injOn_of_minRank {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
  (delta : V → Fin k → V) (w : List (Fin k))
  (hcard : (Finset.univ.image (fun v => List.foldl delta v w)).card =
    rc_minRank delta) (u : List (Fin k)) :
  Set.InjOn (fun x => List.foldl delta x u)
    (Finset.univ.image (fun v => List.foldl delta v w)) ∧
    (Finset.univ.image (fun v => List.foldl delta v (w ++ u))).card =
      rc_minRank delta := by
  classical
  have hJ : (Finset.univ.image (fun v => List.foldl delta v w)).image
    (fun x => List.foldl delta x u) =
    Finset.univ.image (fun v => List.foldl delta v (w ++ u)) :=
    rc_image_append delta w u
  have hge : rc_minRank delta ≤
    ((Finset.univ.image (fun v => List.foldl delta v w)).image
      (fun x => List.foldl delta x u)).card := by
    rw [hJ]
    exact rc_minRank_le delta (w ++ u)
  have hle : ((Finset.univ.image (fun v => List.foldl delta v w)).image
    (fun x => List.foldl delta x u)).card ≤
    (Finset.univ.image (fun v => List.foldl delta v w)).card :=
    Finset.card_image_le
  have hJcard : ((Finset.univ.image (fun v => List.foldl delta v w)).image
    (fun x => List.foldl delta x u)).card = rc_minRank delta := by
    omega
  refine ⟨Finset.card_image_iff.mp (by omega), by rw [← hJ]; exact hJcard⟩

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_stable_of_one_difference](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_stable_of_one_difference {V : Type*} [Fintype V] [DecidableEq V]
  {k : ℕ} (delta : V → Fin k → V) (C : Finset V) (x y : V)
  (hx : x ∉ C) (hy : y ∉ C) (hxy : x ≠ y)
  (w₁ w₂ : List (Fin k))
  (h1 : Finset.univ.image (fun v => List.foldl delta v w₁) = insert x C)
  (h2 : Finset.univ.image (fun v => List.foldl delta v w₂) = insert y C)
  (hc1 : (Finset.univ.image (fun v => List.foldl delta v w₁)).card =
    rc_minRank delta)
  (hc2 : (Finset.univ.image (fun v => List.foldl delta v w₂)).card =
    rc_minRank delta) :
  rc_stable delta x y := by
  classical
  intro u
  by_contra hcon
  have hnon : ∀ v : List (Fin k),
    List.foldl delta x (u ++ v) ≠ List.foldl delta y (u ++ v) :=
    fun v h => hcon ⟨v, h⟩
  have e1 : ∀ v : List (Fin k), List.foldl delta x (u ++ v) =
    List.foldl delta (List.foldl delta x u) v := by
    intro v
    rw [List.foldl_append]
  have e2 : ∀ v : List (Fin k), List.foldl delta y (u ++ v) =
    List.foldl delta (List.foldl delta y u) v := by
    intro v
    rw [List.foldl_append]
  have hnon' : ∀ v : List (Fin k), List.foldl delta (List.foldl delta x u) v ≠
    List.foldl delta (List.foldl delta y u) v := by
    intro v hmerge
    apply hnon v
    rwa [e1, e2]
  obtain ⟨hinj1, hcard1⟩ := rc_injOn_of_minRank delta w₁ hc1 u
  obtain ⟨hinj2, hcard2⟩ := rc_injOn_of_minRank delta w₂ hc2 u
  have hxw1 : x ∈ Finset.univ.image (fun v => List.foldl delta v w₁) := by
    rw [h1]
    exact Finset.mem_insert_self x C
  have hyw2 : y ∈ Finset.univ.image (fun v => List.foldl delta v w₂) := by
    rw [h2]
    exact Finset.mem_insert_self y C
  have hCw1 : ∀ c ∈ C,
    c ∈ Finset.univ.image (fun v => List.foldl delta v w₁) := by
    intro c hc
    rw [h1]
    exact Finset.mem_insert_of_mem hc
  have hCw2 : ∀ c ∈ C,
    c ∈ Finset.univ.image (fun v => List.foldl delta v w₂) := by
    intro c hc
    rw [h2]
    exact Finset.mem_insert_of_mem hc
  have hxy' : List.foldl delta x u ≠ List.foldl delta y u := by
    have h := hnon []
    rwa [List.append_nil] at h
  have hxC' : List.foldl delta x u ∉ C.image (fun z => List.foldl delta z u) := by
    intro hmem
    obtain ⟨c, hc, hfc⟩ := Finset.mem_image.mp hmem
    have hceq : c = x :=
      hinj1 (Finset.mem_coe.mpr (hCw1 c hc)) (Finset.mem_coe.mpr hxw1) hfc
    rw [hceq] at hc
    exact hx hc
  have hyC' : List.foldl delta y u ∉ C.image (fun z => List.foldl delta z u) := by
    intro hmem
    obtain ⟨c, hc, hfc⟩ := Finset.mem_image.mp hmem
    have hceq : c = y :=
      hinj2 (Finset.mem_coe.mpr (hCw2 c hc)) (Finset.mem_coe.mpr hyw2) hfc
    rw [hceq] at hc
    exact hy hc
  have hinjJ1 : ∀ a b : V,
    a ∈ (Finset.univ.image (fun v => List.foldl delta v w₁)).image
      (fun z => List.foldl delta z u) →
    b ∈ (Finset.univ.image (fun v => List.foldl delta v w₁)).image
      (fun z => List.foldl delta z u) →
    ∀ v : List (Fin k), List.foldl delta a v = List.foldl delta b v → a = b := by
    intro a b ha hb v heq
    have hJ : (Finset.univ.image (fun v => List.foldl delta v w₁)).image
      (fun z => List.foldl delta z u) =
      Finset.univ.image (fun v => List.foldl delta v (w₁ ++ u)) :=
      rc_image_append delta w₁ u
    rw [hJ] at ha hb
    obtain ⟨hinj, _⟩ := rc_injOn_of_minRank delta (w₁ ++ u) hcard1 v
    exact hinj (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) heq
  have hinjJ2 : ∀ a b : V,
    a ∈ (Finset.univ.image (fun v => List.foldl delta v w₂)).image
      (fun z => List.foldl delta z u) →
    b ∈ (Finset.univ.image (fun v => List.foldl delta v w₂)).image
      (fun z => List.foldl delta z u) →
    ∀ v : List (Fin k), List.foldl delta a v = List.foldl delta b v → a = b := by
    intro a b ha hb v heq
    have hJ : (Finset.univ.image (fun v => List.foldl delta v w₂)).image
      (fun z => List.foldl delta z u) =
      Finset.univ.image (fun v => List.foldl delta v (w₂ ++ u)) :=
      rc_image_append delta w₂ u
    rw [hJ] at ha hb
    obtain ⟨hinj, _⟩ := rc_injOn_of_minRank delta (w₂ ++ u) hcard2 v
    exact hinj (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) heq
  have hxJ1 : List.foldl delta x u ∈
    (Finset.univ.image (fun v => List.foldl delta v w₁)).image
      (fun z => List.foldl delta z u) :=
    Finset.mem_image.mpr ⟨x, hxw1, rfl⟩
  have hyJ2 : List.foldl delta y u ∈
    (Finset.univ.image (fun v => List.foldl delta v w₂)).image
      (fun z => List.foldl delta z u) :=
    Finset.mem_image.mpr ⟨y, hyw2, rfl⟩
  have hCJ1 : ∀ b ∈ C.image (fun z => List.foldl delta z u),
    b ∈ (Finset.univ.image (fun v => List.foldl delta v w₁)).image
      (fun z => List.foldl delta z u) := by
    intro b hb
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_image.mpr ⟨c, hCw1 c hc, rfl⟩
  have hCJ2 : ∀ b ∈ C.image (fun z => List.foldl delta z u),
    b ∈ (Finset.univ.image (fun v => List.foldl delta v w₂)).image
      (fun z => List.foldl delta z u) := by
    intro b hb
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_image.mpr ⟨c, hCw2 c hc, rfl⟩
  have hno : ∀ a ∈ insert (List.foldl delta y u)
    (insert (List.foldl delta x u) (C.image (fun z => List.foldl delta z u))),
    ∀ b ∈ insert (List.foldl delta y u)
      (insert (List.foldl delta x u) (C.image (fun z => List.foldl delta z u))),
    ∀ v : List (Fin k),
      List.foldl delta a v = List.foldl delta b v → a = b := by
    intro a ha b hb v heq
    rw [Finset.mem_insert] at ha hb
    obtain rfl | ha := ha
    · rcases hb with rfl | hb
      · rfl
      · rw [Finset.mem_insert] at hb
        obtain rfl | hb := hb
        · exact absurd heq.symm (hnon' v)
        · exact hinjJ2 _ _ hyJ2 (hCJ2 _ hb) v heq
    · rw [Finset.mem_insert] at ha
      obtain rfl | hb := hb
      · rcases ha with rfl | ha
        · exact absurd heq (hnon' v)
        · exact hinjJ2 _ _ (hCJ2 _ ha) hyJ2 v heq
      · rw [Finset.mem_insert] at hb
        obtain rfl | ha := ha
        · rcases hb with rfl | hb
          · rfl
          · exact hinjJ1 _ _ hxJ1 (hCJ1 _ hb) v heq
        · rcases hb with rfl | hb
          · exact hinjJ1 _ _ (hCJ1 _ ha) hxJ1 v heq
          · exact hinjJ1 _ _ (hCJ1 _ ha) (hCJ1 _ hb) v heq
  have hsub_eq : insert (List.foldl delta x u)
    (C.image (fun z => List.foldl delta z u)) =
    (Finset.univ.image (fun v => List.foldl delta v w₁)).image
      (fun z => List.foldl delta z u) := by
    ext z
    constructor
    · intro hz
      rw [Finset.mem_insert] at hz
      obtain rfl | hz := hz
      · exact Finset.mem_image.mpr ⟨x, hxw1, rfl⟩
      · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hz
        exact Finset.mem_image.mpr ⟨c, hCw1 c hc, rfl⟩
    · intro hz
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hz
      rw [h1, Finset.mem_insert] at hc
      obtain rfl | hc := hc
      · rw [Finset.mem_insert]
        exact Or.inl rfl
      · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨c, hc, rfl⟩)
  have hmin_sub : (insert (List.foldl delta x u)
    (C.image (fun z => List.foldl delta z u))).card = rc_minRank delta := by
    rwa [hsub_eq, rc_image_append delta w₁ u]
  have hTss : insert (List.foldl delta x u)
    (C.image (fun z => List.foldl delta z u)) ⊂
    insert (List.foldl delta y u)
      (insert (List.foldl delta x u)
        (C.image (fun z => List.foldl delta z u))) :=
    ⟨Finset.subset_insert _ _, fun hcon => by
      have ymem : List.foldl delta y u ∈ insert (List.foldl delta y u)
        (insert (List.foldl delta x u)
          (C.image (fun z => List.foldl delta z u))) :=
        Finset.mem_insert_self _ _
      have ynot : List.foldl delta y u ∉ insert (List.foldl delta x u)
        (C.image (fun z => List.foldl delta z u)) := by
        rw [Finset.mem_insert]
        intro h
        obtain heq | hmem := h
        · exact hxy' heq.symm
        · exact hyC' hmem
      exact ynot (hcon ymem)⟩
  obtain ⟨w₀, hw₀⟩ := rc_minRank_attained delta
  have hinjT : Set.InjOn (fun z => List.foldl delta z w₀)
    ↑(insert (List.foldl delta y u)
      (insert (List.foldl delta x u)
        (C.image (fun z => List.foldl delta z u)))) := by
    intro a ha b hb hab
    exact hno a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) w₀ hab
  have hTimg : ((insert (List.foldl delta y u)
    (insert (List.foldl delta x u)
      (C.image (fun z => List.foldl delta z u)))).image
    (fun z => List.foldl delta z w₀)).card =
    (insert (List.foldl delta y u)
      (insert (List.foldl delta x u)
        (C.image (fun z => List.foldl delta z u)))).card :=
    Finset.card_image_iff.mpr hinjT
  have hTsub : (insert (List.foldl delta y u)
    (insert (List.foldl delta x u)
      (C.image (fun z => List.foldl delta z u)))).image
    (fun z => List.foldl delta z w₀) ⊆
    Finset.univ.image (fun v => List.foldl delta v w₀) := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
  have hTcard_le : (insert (List.foldl delta y u)
    (insert (List.foldl delta x u)
      (C.image (fun z => List.foldl delta z u)))).card ≤
    rc_minRank delta := by
    have h := Finset.card_le_card hTsub
    omega
  have hTgt := Finset.card_lt_card hTss
  omega

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_mem_minRank_image](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_mem_minRank_image {V : Type*} [Fintype V] [DecidableEq V]
  {k : ℕ} (delta : V → Fin k → V) (hcon : rc_strongly delta) (p : V) :
  ∃ w : List (Fin k),
    (Finset.univ.image (fun v => List.foldl delta v w)).card = rc_minRank delta ∧
    p ∈ Finset.univ.image (fun v => List.foldl delta v w) := by
  classical
  obtain ⟨w₀, hw₀⟩ := rc_minRank_attained delta
  obtain ⟨t, ht⟩ := rc_exists_word_of_reflTransGen delta (hcon (List.foldl delta p w₀) p)
  refine ⟨w₀ ++ t, ?_, ?_⟩
  · have hle1 : ((Finset.univ.image (fun v => List.foldl delta v w₀)).image
    (fun x => List.foldl delta x t)).card ≤ rc_minRank delta := by
    rwa [← hw₀]
    have hle2 : rc_minRank delta ≤
      ((Finset.univ.image (fun v => List.foldl delta v w₀)).image
        (fun x => List.foldl delta x t)).card := by
      rw [rc_image_append delta w₀ t]
      exact rc_minRank_le delta (w₀ ++ t)
    rw [← rc_image_append delta w₀ t]
    exact Nat.le_antisymm hle1 hle2
  · refine Finset.mem_image.mpr ⟨p, Finset.mem_univ p, ?_⟩
    rwa [List.foldl_append]

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_exists_stable_pair_of_good_letter](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_exists_stable_pair_of_good_letter {V : Type*} [Finite V]
  {k : ℕ} (delta : V → Fin k → V)
  (hcon : rc_strongly delta) (a : Fin k) (f : V → V) (hf : ∀ v, f v = delta v a)
  (L : ℕ) (hL : 1 ≤ L) (r p : V)
  (hper : ∀ v, f^[L] v ∈ Function.periodicPts f)
  (htop : f^[L - 1] p ∉ Function.periodicPts f)
  (hcoll : ∀ v, f^[L - 1] v ∉ Function.periodicPts f → f^[L] v = r) :
  ∃ x y, x ≠ y ∧ rc_stable delta x y := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have hrep : ∀ j (v : V),
    List.foldl delta v (List.replicate j a) = f^[j] v := by
    intro j
    induction j with
    | zero =>
      intro v
      rfl
    | succ j ih =>
      intro v
      have ih' := ih (f v)
      rw [List.replicate_succ, List.foldl_cons, ← hf v, ih',
        Function.iterate_succ_apply]
  set N : ℕ := Nat.factorial (Fintype.card V) with hN
  have hN1 : 1 ≤ N := by
    rw [hN]
    exact Nat.succ_le_of_lt (Nat.factorial_pos _)
  have hfix : ∀ z ∈ Function.periodicPts f, f^[N] z = z := by
    intro z hz
    obtain ⟨n, hn_pos, hn⟩ := Function.mem_periodicPts.mp hz
    have hmpos : 0 < Function.minimalPeriod f z :=
      Function.minimalPeriod_pos_of_mem_periodicPts hz
    have hmdvd : Function.minimalPeriod f z ∣ n :=
      Function.IsPeriodicPt.minimalPeriod_dvd hn
    have hmle : Function.minimalPeriod f z ≤ Fintype.card V :=
      Function.minimalPeriod_le_card
    have hfact : Function.minimalPeriod f z ∣ N := by
      rw [hN]
      exact Nat.dvd_factorial hmpos hmle
    obtain ⟨t, ht⟩ := hfact
    have hper' : Function.IsPeriodicPt f (Function.minimalPeriod f z * t) z :=
      Function.isPeriodicPt_iff_minimalPeriod_dvd.mpr (Nat.dvd_mul_right _ _)
    rwa [← ht] at hper'
  obtain ⟨w, hwcard, hpmem⟩ := rc_mem_minRank_image delta hcon p
  set J : Finset V := Finset.univ.image (fun v => List.foldl delta v w) with hJ
  obtain ⟨hinjA, hcardA⟩ := rc_injOn_of_minRank delta w hwcard
    (List.replicate (L - 1) a)
  obtain ⟨hinjB, hcardB⟩ := rc_injOn_of_minRank delta w hwcard
    (List.replicate (L - 1 + N) a)
  have e1 : J.image (fun z => f^[L - 1] z) =
    Finset.univ.image (fun v => List.foldl delta v
      (w ++ List.replicate (L - 1) a)) := by
    have hb : ∀ z : V, f^[L - 1] z =
      List.foldl delta z (List.replicate (L - 1) a) :=
      fun z => (hrep (L - 1) z).symm
    simp only [hb]
    exact rc_image_append delta w (List.replicate (L - 1) a)
  have e2 : J.image (fun z => f^[L - 1 + N] z) =
    Finset.univ.image (fun v => List.foldl delta v
      (w ++ List.replicate (L - 1 + N) a)) := by
    have hb : ∀ z : V, f^[L - 1 + N] z =
      List.foldl delta z (List.replicate (L - 1 + N) a) :=
      fun z => (hrep (L - 1 + N) z).symm
    simp only [hb]
    exact rc_image_append delta w (List.replicate (L - 1 + N) a)
  have hsum : L - 1 + N = (N - 1) + L := by omega
  have hstep : ∀ z : V, f^[L - 1 + N] z = f^[N - 1] (f^[L] z) := by
    intro z
    rw [hsum, Function.iterate_add_apply]
  have hperimg : ∀ z ∈ J, f^[L - 1] z ∈ Function.periodicPts f →
    f^[L - 1 + N] z = f^[L - 1] z := by
    intro z hz hmem
    have e : L - 1 + N = N + (L - 1) := Nat.add_comm _ _
    rw [e, Function.iterate_add_apply]
    exact hfix _ hmem
  have hnonimg : ∀ z ∈ J, f^[L - 1] z ∉ Function.periodicPts f →
    f^[L - 1 + N] z = f^[N - 1] r := by
    intro z hz hnp
    rw [hstep z, hcoll z hnp]
  have huniq : ∀ z ∈ J, f^[L - 1] z ∉ Function.periodicPts f → z = p := by
    intro z hz hnp
    have hzp : f^[L - 1 + N] z = f^[L - 1 + N] p := by
      rw [hnonimg z hz hnp, hnonimg p hpmem htop]
    have hzp' : List.foldl delta z (List.replicate (L - 1 + N) a) =
      List.foldl delta p (List.replicate (L - 1 + N) a) := by
      rwa [hrep (L - 1 + N) z, hrep (L - 1 + N) p]
    exact hinjB (Finset.mem_coe.mpr hz) (Finset.mem_coe.mpr hpmem) hzp'
  have hrper : r ∈ Function.periodicPts f := by
    have hLp := hper p
    rwa [hcoll p htop] at hLp
  have hr'per : f^[N - 1] r ∈ Function.periodicPts f := by
    obtain ⟨n, hn_pos, hn⟩ := Function.mem_periodicPts.mp hrper
    refine Function.mem_periodicPts.mpr ⟨n, hn_pos, ?_⟩
    have e1 := Function.iterate_add_apply f n (N - 1) r
    have e2 := Function.iterate_add_apply f (N - 1) n r
    rw [Nat.add_comm n (N - 1)] at e1
    rw [e2] at e1
    rwa [hn] at e1
  have hxy : f^[L - 1] p ≠ f^[N - 1] r := by
    intro heq
    rw [← heq] at hr'per
    exact htop hr'per
  set C : Finset V := (J.filter
    (fun z => f^[L - 1] z ∈ Function.periodicPts f)).image
    (fun z => f^[L - 1] z) with hC
  have hxC : f^[L - 1] p ∉ C := by
    intro hmem
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hmem
    have hzper : f^[L - 1] z ∈ Function.periodicPts f :=
      (Finset.mem_filter.mp hz).2
    change f^[L - 1] z = f^[L - 1] p at hzx
    rw [hzx] at hzper
    exact htop hzper
  have hr'C : f^[N - 1] r ∉ C := by
    intro hmem
    obtain ⟨z, hz, hzr⟩ := Finset.mem_image.mp hmem
    have hzJ : z ∈ J := (Finset.mem_filter.mp hz).1
    have hzper : f^[L - 1] z ∈ Function.periodicPts f :=
      (Finset.mem_filter.mp hz).2
    change f^[L - 1] z = f^[N - 1] r at hzr
    have e1 : f^[L - 1 + N] z = f^[L - 1 + N] p := by
      rw [hperimg z hzJ hzper, hzr]
      exact (hnonimg p hpmem htop).symm
    have zeq : z = p := hinjB (Finset.mem_coe.mpr hzJ)
      (Finset.mem_coe.mpr hpmem) (by
        change List.foldl delta z (List.replicate (L - 1 + N) a) =
          List.foldl delta p (List.replicate (L - 1 + N) a)
        have h1 := hrep (L - 1 + N) z
        have h2 := hrep (L - 1 + N) p
        rw [h1, h2]
        exact e1)
    have hxp : f^[L - 1] z = f^[L - 1] p :=
      congrArg (fun zz => f^[L - 1] zz) zeq
    rw [hxp] at hzper
    exact htop hzper
  have hJ1eq : J.image (fun z => f^[L - 1] z) = insert (f^[L - 1] p) C := by
    ext z
    constructor
    · intro hz
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      by_cases hpa : f^[L - 1] a ∈ Function.periodicPts f
      · rw [Finset.mem_insert]
        exact Or.inr (Finset.mem_image.mpr
          ⟨a, Finset.mem_filter.mpr ⟨ha, hpa⟩, rfl⟩)
      · have hap : a = p := huniq a ha hpa
        subst hap
        rw [Finset.mem_insert]
        exact Or.inl rfl
    · intro hz
      rw [Finset.mem_insert] at hz
      obtain rfl | hz := hz
      · exact Finset.mem_image.mpr ⟨p, hpmem, rfl⟩
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
        exact Finset.mem_image.mpr ⟨a, (Finset.mem_filter.mp ha).1, rfl⟩
  have hJ2eq : J.image (fun z => f^[L - 1 + N] z) = insert (f^[N - 1] r) C := by
    ext z
    constructor
    · intro hz
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      by_cases hpa : f^[L - 1] a ∈ Function.periodicPts f
      · rw [Finset.mem_insert, hperimg a ha hpa]
        exact Or.inr (Finset.mem_image.mpr
          ⟨a, Finset.mem_filter.mpr ⟨ha, hpa⟩, rfl⟩)
      · rw [Finset.mem_insert, hnonimg a ha hpa]
        exact Or.inl rfl
    · intro hz
      rw [Finset.mem_insert] at hz
      obtain rfl | hz := hz
      · exact Finset.mem_image.mpr ⟨p, hpmem, hnonimg p hpmem htop⟩
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
        exact Finset.mem_image.mpr ⟨a, (Finset.mem_filter.mp ha).1,
          hperimg a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2⟩
  have h1 : Finset.univ.image (fun v => List.foldl delta v
    (w ++ List.replicate (L - 1) a)) = insert (f^[L - 1] p) C := by
    rwa [← e1]
  have h2 : Finset.univ.image (fun v => List.foldl delta v
    (w ++ List.replicate (L - 1 + N) a)) = insert (f^[N - 1] r) C := by
    rwa [← e2]
  exact ⟨f^[L - 1] p, f^[N - 1] r, hxy,
    rc_stable_of_one_difference delta C _ _ hxC hr'C hxy _ _ h1 h2 hcardA hcardB⟩

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_level_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_level_zero_iff {V : Type*} [Finite V] (g : V → V) (v : V) :
  rc_level g v = 0 ↔ v ∈ Function.periodicPts g := by
  classical
  have : Fintype V := Fintype.ofFinite V
  exact Nat.find_eq_zero (p := fun i => g^[i] v ∈ Function.periodicPts g) _

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_periodic_map](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_periodic_map {V : Type*} (g : V → V) {z : V}
  (hz : z ∈ Function.periodicPts g) : g z ∈ Function.periodicPts g := by
  obtain ⟨n, hn_pos, hn⟩ := Function.mem_periodicPts.mp hz
  refine Function.mem_periodicPts.mpr ⟨n, hn_pos, ?_⟩
  change g^[n] (g z) = g z
  have e1 : g^[n + 1] z = g^[n] (g z) := Function.iterate_add_apply g n 1 z
  have e2 : g^[n + 1] z = g (g^[n] z) := by
    rw [show n + 1 = (n).succ from rfl]
    exact Function.iterate_succ_apply' g n z
  rw [e1] at e2
  rw [e2, hn]

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_periodic_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_periodic_iterate {V : Type*} (g : V → V) {z : V}
  (hz : z ∈ Function.periodicPts g) (m : ℕ) :
  g^[m] z ∈ Function.periodicPts g := by
  induction m with
  | zero => simpa using hz
  | succ m ih =>
    have h := rc_periodic_map g ih
    have e : g (g^[m] z) = g^[m + 1] z := by
      rw [show m + 1 = (m).succ from rfl]
      exact (Function.iterate_succ_apply' g m z).symm
    rwa [← e]

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_iterate_succ_right](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_iterate_succ_right {V : Type*} (g : V → V) (j : ℕ) (v : V) :
  g^[j + 1] v = g^[j] (g v) :=
  Function.iterate_add_apply g j 1 v

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_level_le_height](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_level_le_height {V : Type*} [Fintype V] [DecidableEq V]
  (g : V → V) (v : V) : rc_level g v ≤ rc_height g := by
  unfold rc_height
  exact Finset.le_sup (Finset.mem_univ v)

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_height_attained](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_height_attained {V : Type*} [Fintype V] [DecidableEq V]
  [Nonempty V] (g : V → V) :
  ∃ p : V, rc_level g p = rc_height g := by
  classical
  unfold rc_height
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup Finset.univ
    Finset.univ_nonempty (fun v => rc_level g v)
  exact ⟨p, hp.symm⟩

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_cyc_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_cyc_le_card {V : Type*} [Fintype V] [DecidableEq V]
  (g : V → V) : rc_cyc g ≤ Fintype.card V := by
  classical
  unfold rc_cyc
  calc (Finset.univ.filter (fun v => v ∈ Function.periodicPts g)).card
    ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = Fintype.card V := Finset.card_univ

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_quot_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_quot_mk {V : Type*} {k : ℕ} (delta : V → Fin k → V)
  (v : V) (c : Fin k) :
  rc_quot delta (Quotient.mk _ v) c = Quotient.mk _ (delta v c) := by
  rfl

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_adj_quot_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_adj_quot_mk {V : Type*} {k : ℕ} (delta : V → Fin k → V)
  {a b : V} (h : rc_adj delta a b) :
  rc_adj (rc_quot delta) (Quotient.mk _ a) (Quotient.mk _ b) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, by rw [rc_quot_mk]; rw [hc]⟩

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_quot_card_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_quot_card_lt {V : Type*} [Fintype V] {k : ℕ}
  (delta : V → Fin k → V) {x y : V}
  (hxy : x ≠ y) (hst : rc_stable delta x y) :
  Fintype.card (Quotient (rc_stableSetoid delta)) < Fintype.card V := by
  classical
  apply Fintype.card_lt_of_surjective_not_injective (Quotient.mk _)
  · exact Quotient.mk_surjective
  · intro hinj
    exact hxy (hinj (Quotient.sound hst))

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_quot_strongly](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_quot_strongly {V : Type*} {k : ℕ}
  (delta : V → Fin k → V) (hcon : rc_strongly delta) :
  rc_strongly (rc_quot delta) := by
  intro q1 q2
  obtain ⟨v1, hv1⟩ := Quotient.exists_rep q1
  obtain ⟨v2, hv2⟩ := Quotient.exists_rep q2
  subst hv1
  subst hv2
  have h := hcon v1 v2
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih => exact Relation.ReflTransGen.tail ih (rc_adj_quot_mk delta hab)

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_quot_aperiodic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_quot_aperiodic {V : Type*} {k : ℕ}
  (delta : V → Fin k → V) (haper : rc_aperiodic delta) :
  rc_aperiodic (rc_quot delta) := by
  intro d hd
  obtain ⟨u, w, hchain, hlast, hdiv⟩ := haper d hd
  refine ⟨Quotient.mk _ u, w.map (Quotient.mk _), ?_, ?_, ?_⟩
  · have hmap : List.IsChain (fun a b : V =>
    rc_adj (rc_quot delta) (Quotient.mk _ a) (Quotient.mk _ b)) (u :: w) :=
    hchain.imp (fun a b h => rc_adj_quot_mk delta h)
    have h := List.isChain_map_of_isChain (Quotient.mk (rc_stableSetoid delta))
      (fun a b h => h) hmap
    rwa [List.map_cons] at h
  · have hmap : (w.map (Quotient.mk (rc_stableSetoid delta))).getLast? =
    (w.getLast?).map (Quotient.mk (rc_stableSetoid delta)) := by simp
    simp [hmap, hlast]
  · have hlen : (w.map (Quotient.mk (rc_stableSetoid delta))).length = w.length := by
    simp
    rwa [hlen]

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_quot_foldl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_quot_foldl {V : Type*} {k : ℕ} (delta : V → Fin k → V)
  (v : V) (w : List (Fin k)) :
  Quotient.mk (rc_stableSetoid delta) (List.foldl delta v w) =
    List.foldl (rc_quot delta) (Quotient.mk _ v) w := by
  induction w generalizing v with
  | nil => rfl
  | cons c t ih =>
    simp only [List.foldl_cons, rc_quot_mk]
    exact ih _

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_lift_quot_foldl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_lift_quot_foldl {V : Type*} {k : ℕ}
  (delta : V → Fin k → V)
  (sigma' : Quotient (rc_stableSetoid delta) → Equiv.Perm (Fin k))
  (v : V) (w : List (Fin k)) :
  Quotient.mk (rc_stableSetoid delta)
    (List.foldl (rc_recolor delta (fun v => sigma' (Quotient.mk _ v))) v w) =
    List.foldl (rc_recolor (rc_quot delta) sigma') (Quotient.mk _ v) w := by
  induction w generalizing v with
  | nil => rfl
  | cons c t ih =>
    have hstep : Quotient.mk (rc_stableSetoid delta)
      ((rc_recolor delta (fun v => sigma' (Quotient.mk _ v))) v c) =
      (rc_recolor (rc_quot delta) sigma') (Quotient.mk _ v) c := by
      change Quotient.mk (rc_stableSetoid delta)
        (delta v (sigma' (Quotient.mk _ v) c)) =
        rc_quot delta (Quotient.mk _ v) (sigma' (Quotient.mk _ v) c)
      exact rc_quot_mk delta v _
    simp only [List.foldl_cons]
    rw [← hstep]
    exact ih _

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_update_iterate_agree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_update_iterate_agree {V : Type*} [DecidableEq V] (R : V → V)
  (x y : V) (v : V) (havoid : ∀ i : ℕ, R^[i] v ≠ x) (j : ℕ) :
  (Function.update R x y)^[j] v = R^[j] v := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have e1 : (Function.update R x y)^[j + 1] v =
      Function.update R x y ((Function.update R x y)^[j] v) := by
      rw [show j + 1 = (j).succ from rfl]
      exact Function.iterate_succ_apply' _ j v
    have e2 : R^[j + 1] v = R (R^[j] v) := by
      rw [show j + 1 = (j).succ from rfl]
      exact Function.iterate_succ_apply' _ j v
    rw [e1, e2, ih]
    exact Function.update_of_ne (havoid j) y R

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_update_periodic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_update_periodic {V : Type*} [DecidableEq V] (R : V → V) (x y : V)
  (z : V) (havoid : ∀ i : ℕ, R^[i] z ≠ x) (hper : z ∈ Function.periodicPts R) :
  z ∈ Function.periodicPts (Function.update R x y) := by
  obtain ⟨n, hn_pos, hn⟩ := Function.mem_periodicPts.mp hper
  refine Function.mem_periodicPts.mpr ⟨n, hn_pos, ?_⟩
  change (Function.update R x y)^[n] z = z
  rwa [rc_update_iterate_agree R x y z havoid n]

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_update_periodic_of](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_update_periodic_of {V : Type*} [DecidableEq V] (R : V → V)
  (x y : V) (w : V)
  (hagree : ∀ j : ℕ, (Function.update R x y)^[j] w = R^[j] w)
  (hper : w ∈ Function.periodicPts (Function.update R x y)) :
  w ∈ Function.periodicPts R := by
  obtain ⟨n, hn_pos, hn⟩ := Function.mem_periodicPts.mp hper
  refine Function.mem_periodicPts.mpr ⟨n, hn_pos, ?_⟩
  change R^[n] w = w
  rwa [← hagree n]

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_ssg_through_edge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_ssg_through_edge {V : Type*} {k : ℕ}
  (delta : V → Fin k → V) (a : Fin k) {v₀ w₀ : V} (h : rc_adj delta v₀ w₀) :
  ∃ g : V → V, (∀ v : V, rc_adj delta v (g v)) ∧ g v₀ = w₀ := by
  classical
  refine ⟨Function.update (fun v => delta v a) v₀ w₀, ?_, Function.update_self _ _ _⟩
  intro v
  by_cases hv : v = v₀
  · subst hv
    rwa [Function.update_self]
  · rw [Function.update_of_ne hv]
    exact ⟨a, rfl⟩

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_height_max_exists](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_height_max_exists {V : Type*} [Fintype V] [DecidableEq V]
  {k : ℕ} (delta : V → Fin k → V) (a : Fin k) :
  ∃ R : V → V, rc_isSSG delta R ∧
    ∀ g : V → V, rc_isSSG delta g → rc_height g ≤ rc_height R := by
  classical
  have hne : (Finset.univ.filter
    (fun g : V → V => ∀ v, rc_adj delta v (g v))).Nonempty := by
    refine ⟨fun v => delta v a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro v
    exact ⟨a, rfl⟩
  obtain ⟨R, hRmem, hRmax⟩ := Finset.exists_max_image _ (fun g => rc_height g) hne
  have hRssg : rc_isSSG delta R := (Finset.mem_filter.mp hRmem).2
  refine ⟨R, hRssg, ?_⟩
  intro g hg
  have hmem : g ∈ Finset.univ.filter
    (fun g : V → V => ∀ v, rc_adj delta v (g v)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ g, hg⟩
  exact hRmax g hmem

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_cyc_max_exists](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_cyc_max_exists {V : Type*} [Fintype V] [DecidableEq V]
  {k : ℕ} (delta : V → Fin k → V) (H : ℕ) (R₀ : V → V)
  (hR₀ : rc_isSSG delta R₀ ∧ rc_height R₀ = H) :
  ∃ R : V → V, rc_isSSG delta R ∧ rc_height R = H ∧
    ∀ g : V → V, rc_isSSG delta g → rc_height g = H → rc_cyc g ≤ rc_cyc R := by
  classical
  have hne : (Finset.univ.filter
    (fun g : V → V => (∀ v, rc_adj delta v (g v)) ∧ rc_height g = H)).Nonempty := by
    refine ⟨R₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hR₀.1, hR₀.2⟩⟩
  obtain ⟨R, hRmem, hRmax⟩ := Finset.exists_max_image _ (fun g => rc_cyc g) hne
  obtain ⟨-, hRssg, hRH⟩ := Finset.mem_filter.mp hRmem
  refine ⟨R, hRssg, hRH, ?_⟩
  intro g hg hHg
  have hmem : g ∈ Finset.univ.filter
    (fun g : V → V => (∀ v, rc_adj delta v (g v)) ∧ rc_height g = H) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ g, hg, hHg⟩
  exact hRmax g hmem

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_lexmax_height_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_lexmax_height_pos {V : Type*} [Fintype V] [DecidableEq V]
  {k : ℕ} (delta : V → Fin k → V) (a : Fin k)
  (hcon : rc_strongly delta) (haper : rc_aperiodic delta)
  (hcard : 1 < Fintype.card V)
  (R : V → V)
  (hHmax : ∀ g : V → V, rc_isSSG delta g → rc_height g ≤ rc_height R) :
  1 ≤ rc_height R := by
  classical
  by_contra hcon0
  have hH0 : rc_height R = 0 := by omega
  obtain ⟨v, br_a, br_b, hbr⟩ := rc_exists_branching delta hcard hcon haper
  obtain ⟨g, hg, hgv⟩ := rc_ssg_through_edge delta a ⟨br_a, rfl⟩
  have hg0 : rc_height g = 0 := by
    have hle := hHmax g hg
    omega
  have hper_all : ∀ z : V, z ∈ Function.periodicPts g := by
    intro z
    have hlev : rc_level g z = 0 := by
      have hle := rc_level_le_height g z
      omega
    rwa [rc_level_zero_iff] at hlev
  have hsurj : Function.Surjective g := by
    intro w
    obtain ⟨n, hn_pos, hn⟩ := Function.mem_periodicPts.mp (hper_all w)
    cases n with
    | zero => omega
    | succ m =>
      exact ⟨g^[m] w, (Function.iterate_succ_apply' g m w).symm.trans hn⟩
  have hinjg : Function.Injective g := Finite.injective_iff_surjective.mpr hsurj
  obtain ⟨u, hu⟩ := hsurj (delta v br_b)
  have hune : u ≠ v := by
    rintro rfl
    exact hbr (hgv.symm.trans hu)
  have hg'ssg : rc_isSSG delta (Function.update g v (delta v br_b)) := by
    intro z
    by_cases hz : z = v
    · subst hz
      rw [Function.update_self]
      exact ⟨br_b, rfl⟩
    · rw [Function.update_of_ne hz]
      exact hg z
  have hcoll : Function.update g v (delta v br_b) u =
    Function.update g v (delta v br_b) v := by
    rwa [Function.update_of_ne hune, Function.update_self]
  have hninj : ¬ Function.Injective (Function.update g v (delta v br_b)) := by
    intro hinj
    exact hune (hinj hcoll)
  have hnsurj : ¬ Function.Surjective (Function.update g v (delta v br_b)) :=
    fun hsurj => hninj (Finite.injective_iff_surjective.mpr hsurj)
  obtain ⟨z, hz⟩ : ∃ z, ∀ w, Function.update g v (delta v br_b) w ≠ z := by
    by_contra hcon2
    apply hnsurj
    intro w
    by_contra hcon3
    apply hcon2
    exact ⟨w, fun w' hw' => hcon3 ⟨w', hw'⟩⟩
  have hznonper : z ∉ Function.periodicPts (Function.update g v (delta v br_b)) := by
    intro hper
    obtain ⟨n, hn_pos, hn⟩ := Function.mem_periodicPts.mp hper
    cases n with
    | zero => omega
    | succ m =>
      exact hz _ ((Function.iterate_succ_apply' _ m z).symm.trans hn)
  have hlev : 1 ≤ rc_level (Function.update g v (delta v br_b)) z := by
    by_contra hcon4
    have h0 : rc_level (Function.update g v (delta v br_b)) z = 0 := by omega
    rw [rc_level_zero_iff] at h0
    exact hznonper h0
  have hge1 : 1 ≤ rc_height (Function.update g v (delta v br_b)) :=
    le_trans hlev (rc_level_le_height _ z)
  have hle := hHmax _ hg'ssg
  omega

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_stable_of_two_bunches](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_stable_of_two_bunches {V : Type*} {k : ℕ} (delta : V → Fin k → V)
  (a₀ : Fin k) {x y z : V}
  (hx : rc_isBunch delta x z) (hy : rc_isBunch delta y z) :
  rc_stable delta x y := by
  intro u
  cases u with
  | nil =>
    refine ⟨[a₀], ?_⟩
    have ex : List.foldl delta x [a₀] = z := by
      rw [List.foldl_cons, List.foldl_nil]
      exact hx a₀
    have ey : List.foldl delta y [a₀] = z := by
      rw [List.foldl_cons, List.foldl_nil]
      exact hy a₀
    simpa using ex.trans ey.symm
  | cons a t =>
    refine ⟨[], ?_⟩
    have ex : List.foldl delta x (a :: t) = List.foldl delta z t := by
      rw [List.foldl_cons, hx a]
    have ey : List.foldl delta y (a :: t) = List.foldl delta z t := by
      rw [List.foldl_cons, hy a]
    simpa using ex.trans ey.symm

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_bunch_recolor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_bunch_recolor {V : Type*} {k : ℕ} (delta : V → Fin k → V)
  (sigma : V → Equiv.Perm (Fin k)) {x z : V} (h : rc_isBunch delta x z) :
  rc_isBunch (rc_recolor delta sigma) x z := by
  intro a
  exact h (sigma x a)

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_cyc_gt_of_subset_ne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_cyc_gt_of_subset_ne {V : Type*} [Fintype V] [DecidableEq V]
  (R R' : V → V)
  (hsub : ∀ z : V, z ∈ Function.periodicPts R → z ∈ Function.periodicPts R')
  (z₀ : V) (hmem : z₀ ∈ Function.periodicPts R') (hne : z₀ ∉ Function.periodicPts R) :
  rc_cyc R < rc_cyc R' := by
  classical
  unfold rc_cyc
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro z hz
    have hz' := (Finset.mem_filter.mp hz).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, hsub z hz'⟩
  · intro heq
    apply hne
    have hmem' : z₀ ∈ Finset.univ.filter (fun v => v ∈ Function.periodicPts R) := by
      rw [heq]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ z₀, hmem⟩
    exact (Finset.mem_filter.mp hmem').2

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_mem_of_periodic_iterate_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_mem_of_periodic_iterate_mem {V : Type*} (g : V → V) (P : V → Prop)
  (hclosed : ∀ a : V, P a → P (g a)) (z : V) (hz : z ∈ Function.periodicPts g)
  (n : ℕ) (hmem : P (g^[n] z)) : P z := by
  obtain ⟨N, hNpos, hN⟩ := Function.mem_periodicPts.mp hz
  have h1N : 1 ≤ N := hNpos
  have hle : n ≤ N * n := by
    calc n = n * 1 := (Nat.mul_one n).symm
    _ ≤ n * N := Nat.mul_le_mul_left n h1N
    _ = N * n := Nat.mul_comm _ _
  have hz_eq : g^[N * n - n] (g^[n] z) = z := by
    have e1 : g^[N * n - n] (g^[n] z) = g^[N * n - n + n] z :=
      (Function.iterate_add_apply g (N * n - n) n z).symm
    have e2 : N * n - n + n = N * n := Nat.sub_add_cancel hle
    have hper : Function.IsPeriodicPt g (N * n) z := hN.mul_const n
    rwa [e1, e2]
  have hclosed_it : ∀ j : ℕ, P (g^[j] (g^[n] z)) := by
    intro j
    induction j with
    | zero => simpa using hmem
    | succ j ih =>
      rw [show j + 1 = j.succ from rfl, Function.iterate_succ_apply']
      exact hclosed _ ih
  rw [← hz_eq]
  exact hclosed_it (N * n - n)

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_ssg_update_edge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_ssg_update_edge {V : Type*} [DecidableEq V] {k : ℕ}
  (delta : V → Fin k → V)
  (R : V → V) (hR : rc_isSSG delta R) (x p : V) (hx : rc_adj delta x p) :
  rc_isSSG delta (Function.update R x p) := by
  intro z
  by_cases hz : z = x
  · subst hz
    rwa [Function.update_self]
  · rw [Function.update_of_ne hz]
    exact hR z

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_exists_other_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_exists_other_top {V : Type*} [Fintype V] [DecidableEq V]
  (R : V → V) (hH : 1 ≤ rc_height R) (hngR : ¬ rc_good R) (p : V) :
  ∃ q : V, rc_level R q = rc_height R ∧ rc_root R q ≠ rc_root R p := by
  by_contra hcon
  apply hngR
  refine ⟨hH, fun v w hv hw => ?_⟩
  by_contra hne
  by_cases hvp : rc_root R v = rc_root R p
  · exact hcon ⟨w, hw, fun heq => hne (hvp.trans heq.symm)⟩
  · exact hcon ⟨v, hv, hvp⟩

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_cycleFin_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_cycleFin_mem {V : Type*} [DecidableEq V]
  (R : V → V) (r z : V) :
  z ∈ rc_cycleFin R r ↔
    ∃ t : ℕ, t < Function.minimalPeriod R r ∧ R^[t] r = z := by
  unfold rc_cycleFin
  rw [Finset.mem_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, Finset.mem_range.mp ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, Finset.mem_range.mpr ht, rfl⟩

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_cycleFin_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_cycleFin_card {V : Type*} [DecidableEq V]
  (R : V → V) (r : V) :
  (rc_cycleFin R r).card = Function.minimalPeriod R r := by
  unfold rc_cycleFin
  refine (Finset.card_image_of_injOn ?_).trans (Finset.card_range _)
  intro a ha b hb hab
  exact Function.iterate_injOn_Iio_minimalPeriod
    (Finset.mem_range.mp (Finset.mem_coe.mp ha))
    (Finset.mem_range.mp (Finset.mem_coe.mp hb)) hab

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_cycleFin_closed](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_cycleFin_closed {V : Type*} [DecidableEq V]
  (R : V → V) (r : V) (hr : r ∈ Function.periodicPts R)
  (z : V) (hz : z ∈ rc_cycleFin R r) : R z ∈ rc_cycleFin R r := by
  obtain ⟨t, ht, rfl⟩ := (rc_cycleFin_mem R r z).mp hz
  have hmpos : 0 < Function.minimalPeriod R r :=
    Function.minimalPeriod_pos_of_mem_periodicPts hr
  by_cases ht' : t + 1 < Function.minimalPeriod R r
  · refine (rc_cycleFin_mem R r _).mpr
    ⟨t + 1, ht', Function.iterate_succ_apply' R t r⟩
  · have htm : t + 1 = Function.minimalPeriod R r := by omega
    have e : R (R^[t] r) = r := by
      have hper : R^[t + 1] r = r := by
        rwa [htm]
      rwa [show t + 1 = t.succ from rfl, Function.iterate_succ_apply'] at hper
    have hr0 : r ∈ rc_cycleFin R r :=
      (rc_cycleFin_mem R r _).mpr ⟨0, hmpos, rfl⟩
    rwa [e]

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_cycleFin_absorb](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_cycleFin_absorb {V : Type*} [DecidableEq V]
  (R : V → V) (r : V) (hr : r ∈ Function.periodicPts R)
  (z : V) (hz : z ∈ Function.periodicPts R) (s : ℕ)
  (hmem : R^[s] z ∈ rc_cycleFin R r) : z ∈ rc_cycleFin R r := by
  obtain ⟨N, hNpos, hN⟩ := Function.mem_periodicPts.mp hz
  have h1N : 1 ≤ N := hNpos
  have hle : s ≤ N * s := by
    calc s = 1 * s := (one_mul s).symm
    _ ≤ N * s := Nat.mul_le_mul_right s h1N
  have hP : Function.IsPeriodicPt R (N * s) z := hN.mul_const s
  have hz_eq : R^[N * s - s] (R^[s] z) = z := by
    have e1 : R^[N * s - s] (R^[s] z) = R^[N * s - s + s] z :=
      (Function.iterate_add_apply R (N * s - s) s z).symm
    have e2 : N * s - s + s = N * s := Nat.sub_add_cancel hle
    rwa [e1, e2]
  have hclosed_it : ∀ j : ℕ, R^[j] (R^[s] z) ∈ rc_cycleFin R r := by
    intro j
    induction j with
    | zero => simpa using hmem
    | succ j ih =>
      rw [show j + 1 = j.succ from rfl, Function.iterate_succ_apply']
      exact rc_cycleFin_closed R r hr _ ih
  have hfin : R^[N * s - s] (R^[s] z) ∈ rc_cycleFin R r := hclosed_it _
  rwa [hz_eq] at hfin

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_Zpred_closed_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_Zpred_closed_cycle {V : Type*} [Finite V] [DecidableEq V]
  (R : V → V) (p : V) (L : ℕ)
  (j : ℕ) (hjm : j < Function.minimalPeriod R (rc_root R p))
  (x : V) (hxj : R^[j] (rc_root R p) = x)
  (h0L : 0 < L)
  (t : ℕ) (ht : t ≤ j) :
  ((∃ s : ℕ, s < L ∧ R^[s] p = Function.update R x p (R^[t] (rc_root R p))) ∨
    (∃ t' : ℕ, t' ≤ j ∧ R^[t'] (rc_root R p) =
      Function.update R x p (R^[t] (rc_root R p)))) := by
  by_cases htj : t = j
  · rw [htj, hxj, Function.update_self]
    refine Or.inl ⟨0, h0L, ?_⟩
    simp
  · have hne : R^[t] (rc_root R p) ≠ x := by
    intro heq
    rw [← hxj] at heq
    have htm : t < Function.minimalPeriod R (rc_root R p) := by omega
    have htu : t = j :=
      Function.iterate_injOn_Iio_minimalPeriod htm hjm heq
    exact htj htu
    have eR' : Function.update R x p (R^[t] (rc_root R p)) =
      R (R^[t] (rc_root R p)) :=
      Function.update_of_ne hne _ _
    rw [eR']
    have efin : R^[t + 1] (rc_root R p) = R (R^[t] (rc_root R p)) :=
      Function.iterate_succ_apply' R t _
    exact Or.inr ⟨t + 1, by omega, efin⟩

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_R'_agree_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_R'_agree_cycle {V : Type*} [Finite V] [DecidableEq V]
  (R : V → V) (r : V)
  (j : ℕ) (hjm : j < Function.minimalPeriod R r)
  (x p : V) (hxj : R^[j] r = x) :
  ∀ s : ℕ, s ≤ j → (Function.update R x p)^[s] r = R^[s] r := by
  intro s
  induction s with
  | zero => intro _; rfl
  | succ s ih =>
    intro hs
    have hs' : s ≤ j := by omega
    have ih' := ih hs'
    have hne : R^[s] r ≠ x := by
      intro heq
      rw [← hxj] at heq
      have hsm : s < Function.minimalPeriod R r := by omega
      have hsu : s = j :=
        Function.iterate_injOn_Iio_minimalPeriod hsm hjm heq
      omega
    have e1 : (Function.update R x p)^[s + 1] r =
      Function.update R x p ((Function.update R x p)^[s] r) := by
      rw [show s + 1 = s.succ from rfl]
      exact Function.iterate_succ_apply' _ _ _
    have e2 : R^[s + 1] r = R (R^[s] r) := by
      rw [show s + 1 = s.succ from rfl]
      exact Function.iterate_succ_apply' _ _ _
    rw [e1, e2, ih', Function.update_of_ne hne]

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_R'_to_p](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_R'_to_p {V : Type*} [Finite V] [DecidableEq V]
  (R : V → V) (r : V) (j : ℕ) (hjm : j < Function.minimalPeriod R r)
  (x p : V) (hxj : R^[j] r = x) :
  (Function.update R x p)^[j + 1] r = p := by
  have e2a : (Function.update R x p)^[j] r = x := by
    rwa [rc_R'_agree_cycle R r j hjm x p hxj j le_rfl]
  have e : (Function.update R x p)^[j + 1] r =
    Function.update R x p ((Function.update R x p)^[j] r) := by
    rw [show j + 1 = j.succ from rfl]
    exact Function.iterate_succ_apply' _ _ _
  rw [e, e2a]
  exact Function.update_self _ _ _

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_update_iterate_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_update_iterate_one {V : Type*} [DecidableEq V]
  (R : V → V) (x p v : V) :
  (Function.update R x p)^[1] v = Function.update R x p v := by
  rw [show (1 : ℕ) = Nat.succ 0 from rfl, Function.iterate_succ_apply',
    Function.iterate_zero_apply]

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_update_agree_upto](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_update_agree_upto {V : Type*} [DecidableEq V]
  (R : V → V) (x w v : V) (N : ℕ)
  (havoid : ∀ s : ℕ, s < N → R^[s] v ≠ x) :
  ∀ s : ℕ, s ≤ N → (Function.update R x w)^[s] v = R^[s] v := by
  intro s
  induction s with
  | zero => intro _; rfl
  | succ s ih =>
    intro hs
    have hs' : s ≤ N := by omega
    have ih' := ih hs'
    have hne : R^[s] v ≠ x := havoid s (by omega)
    have e1 : (Function.update R x w)^[s + 1] v =
      Function.update R x w ((Function.update R x w)^[s] v) := by
      rw [show s + 1 = s.succ from rfl]
      exact Function.iterate_succ_apply' _ _ _
    have e2 : R^[s + 1] v = R (R^[s] v) := by
      rw [show s + 1 = s.succ from rfl]
      exact Function.iterate_succ_apply' _ _ _
    rw [e1, e2, ih', Function.update_of_ne hne]

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_injOn_periodicPts](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_injOn_periodicPts {V : Type*} (f : V → V) :
  Set.InjOn f ↑(Function.periodicPts f) := by
  intro a ha b hb hab
  obtain ⟨Na, hNa, hNaP⟩ := Function.mem_periodicPts.mp ha
  obtain ⟨Nb, hNb, hNbP⟩ := Function.mem_periodicPts.mp hb
  have hM : f^[Na * Nb] a = a := hNaP.mul_const Nb
  have hM2 : f^[Na * Nb] b = b := by
    have h := hNbP.mul_const Na
    rwa [Nat.mul_comm] at h
  have hNpos : 0 < Na * Nb := Nat.mul_pos hNa hNb
  have e1 : f^[Na * Nb] a = f^[Na * Nb - 1] (f a) := by
    have hdec : Na * Nb = (Na * Nb - 1) + 1 := by omega
    conv_lhs => rw [hdec]
    exact Function.iterate_succ_apply f (Na * Nb - 1) a
  have e2 : f^[Na * Nb] b = f^[Na * Nb - 1] (f b) := by
    have hdec : Na * Nb = (Na * Nb - 1) + 1 := by omega
    conv_lhs => rw [hdec]
    exact Function.iterate_succ_apply f (Na * Nb - 1) b
  rw [hab] at e1
  rwa [← e2, hM, hM2] at e1

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_on_cycle_of_hit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_on_cycle_of_hit {V : Type*} [Finite V]
  (R : V → V) (r : V) (hrper : r ∈ Function.periodicPts R)
  (m : ℕ) (hm : m = Function.minimalPeriod R r)
  (c : V) (hc : R^[m - 1] r = c)
  (z : V) (hz : z ∈ Function.periodicPts R) (i : ℕ) (hi : R^[i] z = c) :
  ∃ t : ℕ, t < m ∧ R^[t] r = z := by
  obtain ⟨N, hNpos, hN⟩ := Function.mem_periodicPts.mp hz
  have hNz : R^[N] z = z := hN
  have hNN : ∀ k : ℕ, R^[N * k] z = z := fun k => hN.mul_const k
  have hi' : R^[i % N] z = c := by
    have e : R^[i] z = R^[i % N] z := by
      have hdec : i % N + N * (i / N) = i := Nat.mod_add_div i N
      conv_lhs => rw [← hdec]
      rw [Function.iterate_add_apply]
      exact congrArg (R^[i % N] ·) (hNN (i / N))
    rwa [← e]
  have hz2 : z = R^[N - i % N] c := by
    have hdec : N = (N - i % N) + i % N := by
      have hlt : i % N < N := Nat.mod_lt _ hNpos
      omega
    have e : R^[N] z = R^[N - i % N] (R^[i % N] z) := by
      conv_lhs => rw [hdec]
      exact Function.iterate_add_apply R (N - i % N) (i % N) z
    rwa [hNz, hi'] at e
  have e2 : R^[N - i % N] c = R^[N - i % N + (m - 1)] r := by
    rw [← hc]
    exact (Function.iterate_add_apply R (N - i % N) (m - 1) r).symm
  rw [e2] at hz2
  have hmpos : 0 < m := by
    rw [hm]
    exact Function.minimalPeriod_pos_of_mem_periodicPts hrper
  refine ⟨(N - i % N + (m - 1)) % m, Nat.mod_lt _ hmpos, ?_⟩
  have hm' : (N - i % N + (m - 1)) % m =
    (N - i % N + (m - 1)) % Function.minimalPeriod R r := by
    rw [← hm]
  have e3 := Function.iterate_mod_minimalPeriod_eq (f := R) (x := r)
    (n := N - i % N + (m - 1))
  rwa [hm', e3]

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_B3_Rc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_B3_Rc {V : Type*} (R : V → V) (r : V)
  (hrper : r ∈ Function.periodicPts R)
  (m : ℕ) (hm : m = Function.minimalPeriod R r)
  (c : V) (hc : R^[m - 1] r = c) :
  R c = r := by
  have hmpos : 0 < m := by
    rw [hm]
    exact Function.minimalPeriod_pos_of_mem_periodicPts hrper
  have hper_m : R^[m] r = r := by
    rwa [hm]
  have hdec : m = (m - 1) + 1 := by omega
  have e2 : R^[m] r = R (R^[m - 1] r) := by
    conv_lhs => rw [hdec]
    exact Function.iterate_succ_apply' R (m - 1) r
  rw [hper_m] at e2
  rwa [hc] at e2

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_B3_Psub](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_B3_Psub {V : Type*} [Finite V] [DecidableEq V]
  (R : V → V) (r : V) (hrper : r ∈ Function.periodicPts R)
  (m : ℕ) (hm : m = Function.minimalPeriod R r)
  (c u : V) (hc : R^[m - 1] r = c)
  (hrper' : r ∈ Function.periodicPts (Function.update R c u)) :
  ∀ z : V, z ∈ Function.periodicPts R →
    z ∈ Function.periodicPts (Function.update R c u) := by
  classical
  intro z hz
  by_cases hit : ∃ i : ℕ, R^[i] z = c
  · obtain ⟨i, hi⟩ := hit
    obtain ⟨t, htm, htz⟩ :=
      rc_on_cycle_of_hit R r hrper m hm c hc z hz i hi
    have hmpos : 0 < m := by
      rw [hm]
      exact Function.minimalPeriod_pos_of_mem_periodicPts hrper
    have eag : (Function.update R c u)^[t] r = R^[t] r :=
      rc_R'_agree_cycle R r (m - 1) (by omega) c u hc t (by omega)
    have hper := rc_periodic_iterate _ hrper' t
    rwa [eag, htz] at hper
  · have havoid : ∀ i : ℕ, R^[i] z ≠ c := fun i hi => hit ⟨i, hi⟩
    exact rc_update_periodic R c u z havoid hz

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_B3_cyc_strict](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_B3_cyc_strict {V : Type*} [Finite V] [DecidableEq V]
  (R : V → V) (c u r : V)
  (hRc : R c = r) (hcP : c ∈ Function.periodicPts R)
  (hu : u ≠ r)
  (hsub : ∀ z : V, z ∈ Function.periodicPts R →
    z ∈ Function.periodicPts (Function.update R c u))
  (heq : Function.periodicPts (Function.update R c u) =
    Function.periodicPts R) :
  False := by
  classical
  have hR'c : Function.update R c u c = u := Function.update_self _ _ _
  have hmapR' : ∀ z ∈ Function.periodicPts R,
    Function.update R c u z ∈ Function.periodicPts R := by
    intro z hz
    have h := rc_periodic_map (Function.update R c u) (hsub z hz)
    rwa [heq] at h
  have hinjR : Set.InjOn R ↑(Function.periodicPts R) :=
    rc_injOn_periodicPts R
  have hinjR' : Set.InjOn (Function.update R c u) ↑(Function.periodicPts R) := by
    have h := rc_injOn_periodicPts (Function.update R c u)
    rwa [heq] at h
  have hsig_inj : Function.Injective
    (fun z : ↥(Function.periodicPts R) =>
      (⟨Function.update R c u z.val, hmapR' z.val z.property⟩ :
        ↥(Function.periodicPts R))) := by
    intro a b hab
    have e : Function.update R c u a.val = Function.update R c u b.val :=
      congrArg Subtype.val hab
    have h := hinjR' a.property b.property e
    exact Subtype.ext h
  have hsig_surj := Finite.injective_iff_surjective.mp hsig_inj
  have htau_c : R c ∈ Function.periodicPts R :=
    rc_periodic_map R hcP
  obtain ⟨z, hz⟩ := hsig_surj ⟨R c, htau_c⟩
  have hzz : Function.update R c u z.val = R c := congrArg Subtype.val hz
  by_cases hzc : z.val = c
  · rw [hzc, hR'c, hRc] at hzz
    exact hu hzz
  · have hag : Function.update R c u z.val = R z.val :=
    Function.update_of_ne hzc _ _
    rw [hag] at hzz
    have hzz2 : z.val = c := hinjR z.property hcP hzz
    exact hzc hzz2

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt.RoadColoring

/--
[rc_B3_reduce](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma rc_B3_reduce {V : Type*} [Finite V] [DecidableEq V]
  (R : V → V) (r : V) (hrper : r ∈ Function.periodicPts R)
  (m : ℕ) (hm : m = Function.minimalPeriod R r) (hmpos : 0 < m)
  (c u : V) (hc : R^[m - 1] r = c) (hcP : c ∈ Function.periodicPts R)
  (hrper' : r ∈ Function.periodicPts (Function.update R c u))
  (w : V) (hw_np : w ∉ Function.periodicPts R)
  (hw_orb : ∃ t : ℕ, (Function.update R c u)^[t] r = w) :
  ∃ s : ℕ, R^[s] u = w := by
  classical
  obtain ⟨t, ht⟩ := hw_orb
  obtain ⟨N', hN'pos, hN'⟩ := Function.mem_periodicPts.mp hrper'
  have hpow : ∀ k : ℕ, (Function.update R c u)^[N' * k] r = r := fun k =>
    hN'.mul_const k
  have hmod : (Function.update R c u)^[t % N'] r = w := by
    have hdec : t = N' * (t / N') + t % N' := by
      have := Nat.mod_add_div t N'
      omega
    have e : (Function.update R c u)^[t] r =
      (Function.update R c u)^[N' * (t / N')]
        ((Function.update R c u)^[t % N'] r) := by
      conv_lhs => rw [hdec]
      exact Function.iterate_add_apply _ _ _ _
    have e2 : (Function.update R c u)^[N' * (t / N')]
      ((Function.update R c u)^[t % N'] r) =
      (Function.update R c u)^[t % N'] r := by
      have f1 := Function.iterate_add_apply (Function.update R c u)
        (N' * (t / N')) (t % N') r
      have f2 := Function.iterate_add_apply (Function.update R c u)
        (t % N') (N' * (t / N')) r
      rw [Nat.add_comm (t % N') (N' * (t / N'))] at f2
      rw [f1] at f2
      rwa [hpow (t / N')] at f2
    rw [e2] at e
    rwa [← e]
  have hge : m ≤ t % N' := by
    by_contra hcon
    have hlt : t % N' < m := by omega
    have eag := rc_R'_agree_cycle R r (m - 1) (by omega) c u hc (t % N')
      (by omega)
    rw [hmod] at eag
    have hper : R^[t % N'] r ∈ Function.periodicPts R :=
      rc_periodic_iterate R hrper _
    rw [← eag] at hper
    exact hw_np hper
  have hmc : (Function.update R c u)^[m - 1] r = c := by
    have eag := rc_R'_agree_cycle R r (m - 1) (by omega) c u hc (m - 1) le_rfl
    rwa [hc] at eag
  have hmR' : (Function.update R c u)^[m] r = u := by
    have hdec : m = (m - 1) + 1 := by omega
    have e : (Function.update R c u)^[m] r =
      Function.update R c u ((Function.update R c u)^[m - 1] r) := by
      conv_lhs => rw [hdec]
      rw [show (m - 1) + 1 = ((m - 1)).succ from rfl]
      exact Function.iterate_succ_apply' _ _ _
    rw [e, hmc]
    exact Function.update_self _ _ _
  have hex : ∃ s : ℕ, (Function.update R c u)^[s] u = w :=
    ⟨t % N' - m, by
      have hdec : t % N' = (t % N' - m) + m := by omega
      have e : (Function.update R c u)^[t % N'] r =
        (Function.update R c u)^[t % N' - m]
          ((Function.update R c u)^[m] r) := by
        conv_lhs => rw [hdec]
        exact Function.iterate_add_apply _ _ _ _
      rw [hmR'] at e
      exact e.symm.trans hmod⟩
  obtain ⟨s, hs, hmins⟩ :
    ∃ s : ℕ, (Function.update R c u)^[s] u = w ∧
      ∀ t' : ℕ, t' < s → (Function.update R c u)^[t'] u ≠ w := by
    refine ⟨Nat.find (p := fun s => (Function.update R c u)^[s] u = w) hex,
      Nat.find_spec (p := fun s => (Function.update R c u)^[s] u = w) hex,
      fun t' ht' =>
        Nat.find_min (p := fun s => (Function.update R c u)^[s] u = w) hex
          ht'⟩
  have hseg : ∀ i' : ℕ, i' ≤ s → (Function.update R c u)^[i'] u ≠ c := by
    intro i' hi' hcon
    have hlt : i' < s := by
      by_contra hc
      have heq : i' = s := by omega
      rw [heq, hs] at hcon
      have hcR : w ∈ Function.periodicPts R := by
        rwa [hcon]
      exact hw_np hcR
    have hback : (Function.update R c u)^[s - i' - 1] u = w := by
      have e1 : (Function.update R c u)^[s] u =
        (Function.update R c u)^[s - i' - 1]
          ((Function.update R c u)^[i' + 1] u) := by
        have hdec : s = (s - i' - 1) + (i' + 1) := by omega
        conv_lhs => rw [hdec]
        exact Function.iterate_add_apply _ _ _ _
      have e2 : (Function.update R c u)^[i' + 1] u = u := by
        have e : (Function.update R c u)^[i' + 1] u =
          Function.update R c u ((Function.update R c u)^[i'] u) := by
          rw [show i' + 1 = i'.succ from rfl]
          exact Function.iterate_succ_apply' _ _ _
        rw [e, hcon]
        exact Function.update_self _ _ _
      rw [e2] at e1
      rwa [← e1]
    have hne := hmins (s - i' - 1) (by omega)
    exact hne hback
  have hagree : ∀ t' : ℕ, t' ≤ s →
    (Function.update R c u)^[t'] u = R^[t'] u := by
    intro t'
    induction t' with
    | zero => intro _; rfl
    | succ k ih =>
      intro ht'
      have hks : k ≤ s := by omega
      have ih' := ih hks
      have hne : R^[k] u ≠ c := by
        intro hcon
        have hcon' : (Function.update R c u)^[k] u = c := by
          rwa [ih']
        exact hseg k hks hcon'
      have e1 : (Function.update R c u)^[k + 1] u =
        Function.update R c u ((Function.update R c u)^[k] u) := by
        rw [show k + 1 = k.succ from rfl]
        exact Function.iterate_succ_apply' _ _ _
      have e2 : R^[k + 1] u = R (R^[k] u) := by
        rw [show k + 1 = k.succ from rfl]
        exact Function.iterate_succ_apply' _ _ _
      rw [e1, e2, ih', Function.update_of_ne hne]
  rw [hagree s le_rfl] at hs
  exact ⟨s, hs⟩

end MetaMathlibExt.RoadColoring

namespace MetaMathlibExt

/--
[roadColoring](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
lemma roadColoring
  :
-- imply
  ∀ {V : Type*} [Fintype V] [Nonempty V]
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
-- proof
  intro V _ _ Adj hcon haper hreg
  exact roadColoring' Adj hcon haper hreg
end


/--
[roadColoring'](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma roadColoring'_eq
  :
-- imply
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
-- proof
  apply MetaMathlibExt.roadColoring'


-- created on 2026-10-20
-- updated on 2026-10-23
