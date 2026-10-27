import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.BinaryMatrixRotationOrbitCount.Part3
open scoped BigOperators
open MetaMathlibExt


namespace MetaMathlibExt

/--
[inv_count](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinaryMatrixRotationOrbitCount.lean)
-/
@[path]
under adding `g` is `2 ^ (|G| / addOrderOf g)`. -/
private lemma inv_count {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] (g : G) :
  (Finset.univ.filter (fun f : G → Bool => ∀ x, f (x + g) = f x)).card
    = 2 ^ (Fintype.card G / addOrderOf g) := by
  classical
  have hpos : 0 < addOrderOf g :=
    Nat.pos_of_dvd_of_pos addOrderOf_dvd_card Fintype.card_pos
  have hquot : Fintype.card (G ⧸ AddSubgroup.zmultiples g)
    = Fintype.card G / addOrderOf g := by
    have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (AddSubgroup.zmultiples g)
    rw [Nat.card_zmultiples, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
    rw [h, Nat.mul_div_cancel _ hpos]
  rw [← Fintype.card_subtype, Fintype.card_congr (invEquiv g), Fintype.card_fun,
    Fintype.card_bool, hquot]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[fixedBy_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinaryMatrixRotationOrbitCount.lean)
-/
@[path]
private lemma fixedBy_card {m n : ℕ} [NeZero m] [NeZero n] (g : Fin m × Fin n) :
  Fintype.card (AddAction.fixedBy (Fin m → Fin n → Bool) g)
    = 2 ^ (Fintype.card (Fin m × Fin n) / addOrderOf g) := by
  classical
  rw [Fintype.card_congr (fixedByEquiv g), ← inv_count g, Fintype.card_subtype]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[sum_reindex_order](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinaryMatrixRotationOrbitCount.lean)
-/
@[path]
orders together via Euler's totient. -/
private lemma sum_reindex_order (M : ℕ) [NeZero M] (h : ℕ → ℕ) :
  ∑ i : Fin M, h (addOrderOf i) = ∑ c ∈ M.divisors, Nat.totient c * h c := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := M.divisors)
    (g := fun i : Fin M => addOrderOf i) (f := fun i => h (addOrderOf i))
    (fun i _ => by
      rw [Nat.mem_divisors]
      exact ⟨by simpa using (addOrderOf_dvd_card (x := i)), NeZero.ne M⟩)]
  apply Finset.sum_congr rfl
  intro c hc
  have hcd : c ∣ M := (Nat.mem_divisors.mp hc).1
  have hc' : c ∣ Fintype.card (Fin M) := by simpa using hcd
  have hcard : (Finset.univ.filter (fun a : Fin M => addOrderOf a = c)).card = c.totient :=
    IsAddCyclic.card_addOrderOf_eq_totient hc'
  have heval : ∀ i ∈ Finset.univ.filter (fun a : Fin M => addOrderOf a = c),
    h (addOrderOf i) = h c := fun i hi => by rw [(Finset.mem_filter.mp hi).2]
  rw [Finset.sum_congr rfl heval, Finset.sum_const, hcard, smul_eq_mul]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[burnside_sum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinaryMatrixRotationOrbitCount.lean)
-/
@[path]
private lemma burnside_sum_eq {m n : ℕ} [NeZero m] [NeZero n] :
  ∑ g : Fin m × Fin n, Fintype.card (AddAction.fixedBy (Fin m → Fin n → Bool) g)
    = ∑ c ∈ m.divisors, ∑ d ∈ n.divisors,
      Nat.totient c * Nat.totient d * 2 ^ (m * n / Nat.lcm c d) := by
  have hcardG : Fintype.card (Fin m × Fin n) = m * n := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  calc ∑ g : Fin m × Fin n, Fintype.card (AddAction.fixedBy (Fin m → Fin n → Bool) g)
    = ∑ g : Fin m × Fin n, 2 ^ (m * n / addOrderOf g) := by
      apply Finset.sum_congr rfl; intro g _; rw [fixedBy_card, hcardG]
    _ = ∑ i : Fin m, ∑ j : Fin n, 2 ^ (m * n / Nat.lcm (addOrderOf i) (addOrderOf j)) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [Prod.addOrderOf_mk]
    _ = ∑ i : Fin m, ∑ d ∈ n.divisors,
      Nat.totient d * 2 ^ (m * n / Nat.lcm (addOrderOf i) d) := by
      apply Finset.sum_congr rfl; intro i _
      exact sum_reindex_order n (fun d => 2 ^ (m * n / Nat.lcm (addOrderOf i) d))
    _ = ∑ c ∈ m.divisors, Nat.totient c *
      (∑ d ∈ n.divisors, Nat.totient d * 2 ^ (m * n / Nat.lcm c d)) :=
      sum_reindex_order m
        (fun c => ∑ d ∈ n.divisors, Nat.totient d * 2 ^ (m * n / Nat.lcm c d))
    _ = ∑ c ∈ m.divisors, ∑ d ∈ n.divisors,
      Nat.totient c * Nat.totient d * 2 ^ (m * n / Nat.lcm c d) := by
      apply Finset.sum_congr rfl; intro c _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro d _
      rw [← mul_assoc]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[e_inj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinaryMatrixRotationOrbitCount.lean)
-/
@[path]
private lemma e_inj (m n : ℕ) :
  Function.Injective (fun p : Fin m × Fin n => p.1.val * n + p.2.val) := by
  intro a b hab
  apply finProdFinEquiv.injective
  apply Fin.val_injective
  rw [finProdFinEquiv_apply_val, finProdFinEquiv_apply_val]
  simp only at hab
  rw [Nat.mul_comm a.1.val n, Nat.mul_comm b.1.val n] at hab
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Wt_inj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinaryMatrixRotationOrbitCount.lean)
-/
@[path]
private lemma Wt_inj (m n : ℕ) : Function.Injective (Wt m n) := by
  classical
  set e : Fin m × Fin n → ℕ := fun p => p.1.val * n + p.2.val with he
  have einj : Function.Injective e := e_inj m n
  have key : ∀ z : Fin m → Fin n → Bool,
    Wt m n z
      = ∑ k ∈ (Finset.univ.filter (fun p : Fin m × Fin n => z p.1 p.2 = true)).image e,
        2 ^ k := by
    intro z
    rw [Wt, ← Fintype.sum_prod_type (fun p : Fin m × Fin n =>
      (if z p.1 p.2 = true then 1 else 0) * 2 ^ (p.1.val * n + p.2.val))]
    rw [Finset.sum_image (by intro a _ b _ hab; exact einj hab), Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : z p.1 p.2 = true <;> simp [hp, he]
  intro x y hxy
  rw [key x, key y] at hxy
  have hT := congrArg (fun N => N.bitIndices.toFinset) hxy
  simp only [Finset.toFinset_bitIndices_sum_two_pow] at hT
  have hfilter := Finset.image_injective einj hT
  funext r s
  have hiff : (r, s) ∈ Finset.univ.filter (fun p : Fin m × Fin n => x p.1 p.2 = true)
    ↔ (r, s) ∈ Finset.univ.filter (fun p : Fin m × Fin n => y p.1 p.2 = true) := by
    rw [hfilter]
  simpa using hiff

end MetaMathlibExt

namespace MetaMathlibExt

/--
[orbit_min_count](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinaryMatrixRotationOrbitCount.lean)
-/
@[path]
the orbits. -/
private lemma orbit_min_count (m n : ℕ) [NeZero m] [NeZero n] :
  (Finset.univ.filter (fun x : Fin m → Fin n → Bool =>
    ∀ g : Fin m × Fin n, Wt m n x ≤ Wt m n (g +ᵥ x))).card
    = Nat.card
      (Quotient (AddAction.orbitRel (Fin m × Fin n) (Fin m → Fin n → Bool))) := by
  classical
  set G := Fin m × Fin n
  set Y := Fin m → Fin n → Bool
  set P : Y → Prop := fun x => ∀ g : G, Wt m n x ≤ Wt m n (g +ᵥ x) with hP
  have : Fintype (Quotient (AddAction.orbitRel G Y)) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype P]
  refine Fintype.card_of_bijective
    (f := fun x : {x // P x} => Quotient.mk (AddAction.orbitRel G Y) x.1) ?_
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    have hrel : x ∈ AddAction.orbit G y :=
      AddAction.orbitRel_apply.mp (Quotient.exact hxy)
    obtain ⟨g, hg⟩ := AddAction.mem_orbit_iff.mp hrel
    have hg2 : (-g) +ᵥ x = y := by rw [← hg, ← add_vadd, neg_add_cancel, zero_vadd]
    have h1 : Wt m n x ≤ Wt m n y := by have := hx (-g); rwa [hg2] at this
    have h2 : Wt m n y ≤ Wt m n x := by have := hy g; rwa [hg] at this
    have hxyeq : x = y := Wt_inj m n (le_antisymm h1 h2)
    simpa using hxyeq
  · intro q
    obtain ⟨x₀, hx₀⟩ := Quotient.exists_rep q
    set O := Finset.univ.filter
      (fun z : Y => Quotient.mk (AddAction.orbitRel G Y) z = q) with hO
    have hx₀O : x₀ ∈ O := by rw [hO, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hx₀⟩
    obtain ⟨xm, hxmO, hmin⟩ := Finset.exists_min_image O (Wt m n) ⟨x₀, hx₀O⟩
    have hxmq : Quotient.mk (AddAction.orbitRel G Y) xm = q := (Finset.mem_filter.mp hxmO).2
    refine ⟨⟨xm, ?_⟩, hxmq⟩
    intro g
    apply hmin
    rw [hO, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rwa [← hxmq]
      (AddAction.orbitRel_apply.mpr (AddAction.mem_orbit_iff.mpr ⟨g, rfl⟩))

end MetaMathlibExt

namespace MetaMathlibExt

/--
[binaryMatrixRotationOrbitCount](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinaryMatrixRotationOrbitCount.lean)
-/
@[path]
lemma binaryMatrixRotationOrbitCount
  {m n : ℕ}
-- given
  (hm : 0 < m)
  (hn : 0 < n) :
-- imply
  (Finset.univ.filter (fun x : Fin m → Fin n → Bool =>
    ∀ i : Fin m, ∀ j : Fin n,
    (∑ r : Fin m, ∑ s : Fin n,
    (if x r s = true then 1 else 0) * 2 ^ (r.val * n + s.val)) ≤
    (∑ r : Fin m, ∑ s : Fin n,
    (if x (r + i) (s + j) = true then 1 else 0) *
    2 ^ (r.val * n + s.val)))).card =
    (∑ c ∈ m.divisors, ∑ d ∈ n.divisors,
    Nat.totient c * Nat.totient d *
    2 ^ ((m * n) / Nat.lcm c d)) / (m * n) := by
-- proof
  classical
  have : NeZero m := ⟨hm.ne'⟩
  have : NeZero n := ⟨hn.ne'⟩
  have : Fintype (Quotient
    (AddAction.orbitRel (Fin m × Fin n) (Fin m → Fin n → Bool))) := Fintype.ofFinite _
  have hpred : ∀ x : Fin m → Fin n → Bool,
    (∀ i : Fin m, ∀ j : Fin n,
      (∑ r : Fin m, ∑ s : Fin n,
        (if x r s = true then 1 else 0) * 2 ^ (r.val * n + s.val)) ≤
      (∑ r : Fin m, ∑ s : Fin n,
        (if x (r + i) (s + j) = true then 1 else 0) * 2 ^ (r.val * n + s.val)))
    ↔ (∀ g : Fin m × Fin n, Wt m n x ≤ Wt m n (g +ᵥ x)) :=
    fun x => ⟨fun h g => h g.1 g.2, fun h i j => h (i, j)⟩
  have hfe := Finset.filter_congr (s := Finset.univ) (fun x (_ : x ∈ Finset.univ) => hpred x)
  rw [hfe, orbit_min_count]
  have hburn := AddAction.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup
    (Fin m × Fin n) (Fin m → Fin n → Bool)
  rw [burnside_sum_eq] at hburn
  have hcardG : Fintype.card (Fin m × Fin n) = m * n := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  rw [hcardG] at hburn
  rw [Nat.card_eq_fintype_card, hburn, Nat.mul_div_cancel _ (Nat.mul_pos hm hn)]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
