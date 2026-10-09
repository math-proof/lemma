import Mathlib
import sympy.Basic


/--
[AddMonoidHom_natCard_sq_le_of_isotropic](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AddMonoidHom_natCard_sq_le_of_isotropic.lean)
-/

def orthogonal
  {V : Type u}
  {Q : Type v}
  [AddCommGroup V]
  [AddCommGroup Q]
  (β : V →+ V →+ Q) (K : AddSubgroup V) : AddSubgroup V where
  carrier := {v | ∀ k ∈ K, β k v = 0}
  zero_mem' := fun k _ => map_zero (β k)
  add_mem' := fun {a b} ha hb k hk => by rw [map_add, ha k hk, hb k hk, add_zero]
  neg_mem' := fun {a} ha k hk => by rw [map_neg, ha k hk, neg_zero]

private lemma nsmul_natCard_eq_zero
  {A : Type u} [AddCommGroup A] [Finite A] (a : A) : Nat.card A • a = 0 :=
  addOrderOf_dvd_iff_nsmul_eq_zero.1 (addOrderOf_dvd_natCard a)

private lemma finite_torsion_of_encard_le
  {Q : Type v}
  [AddCommGroup Q]
  {n : ℕ} (h : ({x : Q | n • x = 0} : Set Q).encard ≤ n) :
  Finite ↥{x : Q | n • x = 0} :=
  (Set.encard_le_coe_iff_finite_ncard_le.mp h).1.to_subtype

private lemma natCard_torsion_le_of_encard_le
  {Q : Type v}
  [AddCommGroup Q]
  {n : ℕ} (h : ({x : Q | n • x = 0} : Set Q).encard ≤ n) :
  Nat.card ↥{x : Q | n • x = 0} ≤ n :=
  (Set.encard_le_coe_iff_finite_ncard_le.mp h).2

private lemma finite_addMonoidHom
  {Q : Type v}
  [AddCommGroup Q]
  (hQ : ∀ n : ℕ, n ≠ 0 → ({x : Q | n • x = 0} : Set Q).encard ≤ n)
  (A : Type u) [AddCommGroup A] [Finite A] : Finite (A →+ Q) := by
  have := finite_torsion_of_encard_le (hQ (Nat.card A) Nat.card_pos.ne')
  let f : (A →+ Q) → (A → ↥{x : Q | Nat.card A • x = 0}) :=
    fun φ a => ⟨φ a, by
      show Nat.card A • φ a = 0
      rw [← map_nsmul, nsmul_natCard_eq_zero, map_zero]⟩
  refine Finite.of_injective f fun φ ψ h => ?_
  ext a
  exact congrArg Subtype.val (congrFun h a)

private lemma natCard_addMonoidHom_zmultiples_le
  {Q : Type v}
  [AddCommGroup Q]
  (hQ : ∀ n : ℕ, n ≠ 0 → ({x : Q | n • x = 0} : Set Q).encard ≤ n)
  {A : Type u} [AddCommGroup A] [Finite A] (a : A) :
  Nat.card (AddSubgroup.zmultiples a →+ Q) ≤ Nat.card (AddSubgroup.zmultiples a) := by
  have hn : addOrderOf a ≠ 0 := (addOrderOf_pos a).ne'
  have := finite_torsion_of_encard_le (hQ _ hn)
  rw [Nat.card_zmultiples]
  refine le_trans ?_ (natCard_torsion_le_of_encard_le (hQ _ hn))
  let f : (AddSubgroup.zmultiples a →+ Q) → ↥{x : Q | addOrderOf a • x = 0} :=
    fun φ => ⟨φ ⟨a, AddSubgroup.mem_zmultiples a⟩, by
      show addOrderOf a • φ ⟨a, AddSubgroup.mem_zmultiples a⟩ = 0
      rw [← map_nsmul]
      convert map_zero φ
      exact Subtype.ext (addOrderOf_nsmul_eq_zero a)⟩
  refine Nat.card_le_card_of_injective f fun φ ψ h => ?_
  have h1 : φ ⟨a, AddSubgroup.mem_zmultiples a⟩ = ψ ⟨a, AddSubgroup.mem_zmultiples a⟩ :=
    congrArg Subtype.val h
  ext ⟨b, hb⟩
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hb
  have : (⟨k • a, hb⟩ : AddSubgroup.zmultiples a) = k • ⟨a, AddSubgroup.mem_zmultiples a⟩ := rfl
  rw [this, map_zsmul, map_zsmul, h1]

private lemma natCard_addMonoidHom_le
  {Q : Type v}
  [AddCommGroup Q]
  (hQ : ∀ n : ℕ, n ≠ 0 → ({x : Q | n • x = 0} : Set Q).encard ≤ n)
  (A : Type u) [AddCommGroup A] [Finite A] :
  Nat.card (A →+ Q) ≤ Nat.card A := by
  suffices H : ∀ (n : ℕ) (A : Type u) [AddCommGroup A] [Finite A], Nat.card A = n →
      Nat.card (A →+ Q) ≤ Nat.card A from H _ A rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A _ _ hA
    if hs : Subsingleton A then
      have : Subsingleton (A →+ Q) :=
        ⟨fun φ ψ => by ext x; rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
      rw [Nat.card_of_subsingleton (0 : A →+ Q), Nat.card_of_subsingleton (0 : A)]
    else
      obtain ⟨a, ha⟩ : ∃ a : A, a ≠ 0 := by
        by_contra! h; exact hs ⟨fun x y => by rw [h x, h y]⟩
      let B := AddSubgroup.zmultiples a
      have : Finite (A →+ Q) := finite_addMonoidHom hQ A
      have : Finite (B →+ Q) := finite_addMonoidHom hQ B
      have : Finite (A ⧸ B →+ Q) := finite_addMonoidHom hQ (A ⧸ B)

      let res : (A →+ Q) →+ (B →+ Q) :=
        AddMonoidHom.mk' (fun φ => φ.comp B.subtype) (fun φ ψ => AddMonoidHom.add_comp φ ψ _)

      have hcard := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup res.ker
      have h1 : Nat.card ((A →+ Q) ⧸ res.ker) ≤ Nat.card (B →+ Q) := by
        rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange res).toEquiv]
        exact Nat.card_le_card_of_injective _ Subtype.val_injective
      have h2 : Nat.card res.ker ≤ Nat.card (A ⧸ B →+ Q) := by
        let g : res.ker → (A ⧸ B →+ Q) := fun φ =>
          QuotientAddGroup.lift B φ.1 (fun b hb => by
            have := φ.2
            rw [AddMonoidHom.mem_ker] at this
            exact DFunLike.congr_fun this ⟨b, hb⟩)
        refine Nat.card_le_card_of_injective g fun φ ψ h => ?_
        apply Subtype.ext
        ext x
        have hgφ : (g φ) (QuotientAddGroup.mk x) = φ.1 x := rfl
        have hgψ : (g ψ) (QuotientAddGroup.mk x) = ψ.1 x := rfl
        have h3 := DFunLike.congr_fun h (QuotientAddGroup.mk x)
        rwa [hgφ, hgψ] at h3
      have hB : Nat.card (B →+ Q) ≤ Nat.card B := natCard_addMonoidHom_zmultiples_le hQ a
      have hAB : Nat.card (A ⧸ B →+ Q) ≤ Nat.card (A ⧸ B) := by
        refine ih (Nat.card (A ⧸ B)) ?_ (A ⧸ B) rfl
        rw [← hA, AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup B]
        have hB2 : 1 < Nat.card B := by
          rw [Nat.card_zmultiples]
          have h1 := addOrderOf_pos a
          have h2 : addOrderOf a ≠ 1 := fun h => ha (AddMonoid.addOrderOf_eq_one_iff.1 h)
          omega
        have hQpos : 0 < Nat.card (A ⧸ B) := Nat.card_pos
        nlinarith
      calc _ = Nat.card ((A →+ Q) ⧸ res.ker) * Nat.card res.ker := hcard
        _ ≤ Nat.card (B →+ Q) * Nat.card (A ⧸ B →+ Q) := Nat.mul_le_mul h1 h2
        _ ≤ Nat.card B * Nat.card (A ⧸ B) := Nat.mul_le_mul hB hAB
        _ = Nat.card A := by
          rw [mul_comm, ← AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup B]

private lemma encard_torsion_le_of_injective
  {Q : Type v}
  [AddCommGroup Q]
  {Q' : Type w} [AddCommGroup Q'] (ι : Q →+ Q')
  (hι : Function.Injective ι)
  (hQ' : ∀ n : ℕ, n ≠ 0 → ({x : Q' | n • x = 0} : Set Q').encard ≤ n) (n : ℕ) (hn : n ≠ 0) :
  ({x : Q | n • x = 0} : Set Q).encard ≤ n := by
  refine le_trans ?_ (hQ' n hn)
  rw [← hι.encard_image]
  refine Set.encard_le_encard ?_
  rintro _ ⟨x, hx, rfl⟩
  simp only [Set.mem_ofPred_eq] at hx ⊢
  rw [← map_nsmul, hx, map_zero]

private lemma encard_torsion_addCircle_le
  {𝕜 : Type w} [AddCommGroup 𝕜] [IsAddTorsionFree 𝕜] (p : 𝕜)
  (n : ℕ) (hn : n ≠ 0) :
  ({x : AddCircle p | n • x = 0} : Set (AddCircle p)).encard ≤ n :=
  AddCircle.card_torsion_le_of_isSMulRegular p n hn (nsmul_right_injective hn)

private lemma encard_torsion_zmod_le
  {m : ℕ} [NeZero m] (n : ℕ) (hn : n ≠ 0) :
  ({x : ZMod m | n • x = 0} : Set (ZMod m)).encard ≤ n :=
  encard_torsion_le_of_injective ZMod.toAddCircle (ZMod.toAddCircle_injective m)
    (encard_torsion_addCircle_le (1 : ℝ)) n hn

private lemma encard_torsion_additive_units_le
  {L : Type w} [CommRing L] [IsDomain L] (n : ℕ) (hn : n ≠ 0) :
  ({x : Additive Lˣ | n • x = 0} : Set (Additive Lˣ)).encard ≤ n := by
  have : NeZero n := ⟨hn⟩
  let e : ({x : Additive Lˣ | n • x = 0} : Set (Additive Lˣ)) ≃ rootsOfUnity n L :=
    { toFun := fun x => ⟨Additive.toMul x.1, x.2⟩
      invFun := fun u => ⟨Additive.ofMul u.1, u.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hfin : Finite ({x : Additive Lˣ | n • x = 0} : Set (Additive Lˣ)) := Finite.of_equiv _ e.symm
  rw [Set.encard_le_coe_iff_finite_ncard_le, ← Nat.card_coe_set_eq, Nat.card_congr e]
  exact ⟨Set.finite_coe_iff.mp hfin, card_rootsOfUnity (R := L) (k := n)⟩

private lemma encard_torsion_additive_subgroup_units_le
  {L : Type w} [CommRing L] [IsDomain L]
  (S : Subgroup Lˣ) (n : ℕ) (hn : n ≠ 0) :
  ({x : Additive S | n • x = 0} : Set (Additive S)).encard ≤ n :=
  encard_torsion_le_of_injective (MonoidHom.toAdditive S.subtype)
    (fun _ _ h => Subtype.val_injective h) (encard_torsion_additive_units_le (L := L)) n hn

private lemma mem_orthogonal
  {V : Type u}
  {Q : Type v}
  [AddCommGroup V]
  [AddCommGroup Q]
  {β : V →+ V →+ Q} {K : AddSubgroup V} {v : V} :
  v ∈ orthogonal β K ↔ ∀ k ∈ K, β k v = 0 := Iff.rfl

private lemma le_orthogonal_of_isotropic
  {V : Type u}
  {Q : Type v}
  [AddCommGroup V]
  [AddCommGroup Q]
  (β : V →+ V →+ Q) (K : AddSubgroup V)
  (hK : ∀ k ∈ K, ∀ k' ∈ K, β k k' = 0) : K ≤ orthogonal β K :=
  fun v hv k hk => hK k hk v hv

private lemma natCard_le_natCard_addMonoidHom_quotient_orthogonal
  {V : Type u}
  {Q : Type v}
  [AddCommGroup V]
  [AddCommGroup Q]
  (β : V →+ V →+ Q)
  (hβ : ∀ v, β v = 0 → v = 0) (K : AddSubgroup V) [Finite (V ⧸ orthogonal β K →+ Q)] :
  Nat.card K ≤ Nat.card (V ⧸ orthogonal β K →+ Q) := by
  let f : K → (V ⧸ orthogonal β K →+ Q) := fun k =>
    QuotientAddGroup.lift (orthogonal β K) (β k) (fun v hv => AddMonoidHom.mem_ker.mpr (hv k k.2))
  refine Nat.card_le_card_of_injective f fun k₁ k₂ h => ?_
  apply Subtype.ext
  rw [← sub_eq_zero]
  refine hβ _ ?_
  ext v
  have := DFunLike.congr_fun h (QuotientAddGroup.mk v)
  simp only [f, QuotientAddGroup.lift_mk] at this
  rw [map_sub, AddMonoidHom.sub_apply, this, sub_self, AddMonoidHom.zero_apply]

private lemma natCard_sq_le_of_isotropic
  {V : Type u}
  {Q : Type v}
  [AddCommGroup V]
  [AddCommGroup Q]
  [Finite V]
  (hQ : ∀ n : ℕ, n ≠ 0 → ({x : Q | n • x = 0} : Set Q).encard ≤ n)
  (β : V →+ V →+ Q) (hβ : ∀ v, β v = 0 → v = 0)
  (K : AddSubgroup V) (hK : ∀ k ∈ K, ∀ k' ∈ K, β k k' = 0) :
  Nat.card K ^ 2 ≤ Nat.card V := by
  have : Finite (V ⧸ orthogonal β K →+ Q) := finite_addMonoidHom hQ _
  have h1 := natCard_le_natCard_addMonoidHom_quotient_orthogonal β hβ K
  have h2 : Nat.card (V ⧸ orthogonal β K →+ Q) ≤ Nat.card (V ⧸ orthogonal β K) :=
    natCard_addMonoidHom_le hQ _
  have h3 : Nat.card K ≤ Nat.card (orthogonal β K) :=
    Nat.card_le_card_of_injective _
      (AddSubgroup.inclusion_injective (le_orthogonal_of_isotropic β K hK))
  calc _ = Nat.card K * Nat.card K := sq _
    _ ≤ Nat.card (V ⧸ orthogonal β K) * Nat.card (orthogonal β K) := Nat.mul_le_mul (h1.trans h2) h3
    _ = Nat.card V := (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _).symm

private lemma natCard_mul_natCard_le_of_isotropic
  {V : Type u}
  {Q : Type v}
  [AddCommGroup V]
  [AddCommGroup Q]
  [Finite V]
  (hQ : ∀ n : ℕ, n ≠ 0 → ({x : Q | n • x = 0} : Set Q).encard ≤ n)
  (β : V →+ V →+ Q) (hβ : ∀ v, β v = 0 → v = 0)
  (K : AddSubgroup V) (hK : ∀ k ∈ K, ∀ k' ∈ K, β k k' = 0) :
  Nat.card K * Nat.card K ≤ Nat.card V := by
  rw [← sq]; exact natCard_sq_le_of_isotropic hQ β hβ K hK

private lemma natCard_sq_le_of_isotropic_addCircle
  {V : Type u}
  [AddCommGroup V]
  [Finite V]
  {𝕜 : Type w} [AddCommGroup 𝕜] [IsAddTorsionFree 𝕜]
  (p : 𝕜) (β : V →+ V →+ AddCircle p) (hβ : ∀ v, β v = 0 → v = 0)
  (K : AddSubgroup V) (hK : ∀ k ∈ K, ∀ k' ∈ K, β k k' = 0) :
  Nat.card K ^ 2 ≤ Nat.card V :=
  natCard_sq_le_of_isotropic (encard_torsion_addCircle_le p) β hβ K hK

private lemma natCard_sq_le_of_isotropic_zmod
  {V : Type u}
  [AddCommGroup V]
  [Finite V]
  {m : ℕ} [NeZero m]
  (β : V →+ V →+ ZMod m) (hβ : ∀ v, β v = 0 → v = 0)
  (K : AddSubgroup V) (hK : ∀ k ∈ K, ∀ k' ∈ K, β k k' = 0) :
  Nat.card K ^ 2 ≤ Nat.card V :=
  natCard_sq_le_of_isotropic (encard_torsion_zmod_le (m := m)) β hβ K hK

private lemma natCard_sq_le_of_isotropic_of_injective
  {V : Type u}
  {Q : Type v}
  [AddCommGroup V]
  [AddCommGroup Q]
  [Finite V]
  {Q' : Type w} [AddCommGroup Q'] (ι : Q →+ Q')
  (hι : Function.Injective ι)
  (hQ' : ∀ n : ℕ, n ≠ 0 → ({x : Q' | n • x = 0} : Set Q').encard ≤ n)
  (β : V →+ V →+ Q) (hβ : ∀ v, β v = 0 → v = 0)
  (K : AddSubgroup V) (hK : ∀ k ∈ K, ∀ k' ∈ K, β k k' = 0) :
  Nat.card K ^ 2 ≤ Nat.card V :=
  natCard_sq_le_of_isotropic (encard_torsion_le_of_injective ι hι hQ') β hβ K hK

private lemma natCard_sq_le_of_isotropic_units
  {V : Type u}
  [AddCommGroup V]
  [Finite V]
  {L : Type w} [CommRing L] [IsDomain L]
  (β : V →+ V →+ Additive Lˣ) (hβ : ∀ v, β v = 0 → v = 0)
  (K : AddSubgroup V) (hK : ∀ k ∈ K, ∀ k' ∈ K, β k k' = 0) :
  Nat.card K ^ 2 ≤ Nat.card V :=
  natCard_sq_le_of_isotropic (encard_torsion_additive_units_le (L := L)) β hβ K hK

private lemma natCard_sq_le_of_isotropic_subgroup_units
  {V : Type u}
  [AddCommGroup V]
  [Finite V]
  {L : Type w} [CommRing L] [IsDomain L]
  (S : Subgroup Lˣ) (β : V →+ V →+ Additive S) (hβ : ∀ v, β v = 0 → v = 0)
  (K : AddSubgroup V) (hK : ∀ k ∈ K, ∀ k' ∈ K, β k k' = 0) :
  Nat.card K ^ 2 ≤ Nat.card V :=
  natCard_sq_le_of_isotropic (encard_torsion_additive_subgroup_units_le (L := L) S) β hβ K hK

@[path]
private lemma main
  [AddCommGroup V] [Finite V] [AddCommGroup Q]
  {β : V →+ V →+ Q}
  {K : AddSubgroup V}
-- given
  (hβ : ∀ v, β v = 0 → v = 0)
  (hQ : ∀ n : ℕ, n ≠ 0 → {x : Q | n • x = 0}.encard ≤ n)
  (hK : ∀ k ∈ K, ∀ k' ∈ K, β k k' = 0) :
-- imply
  Nat.card K ^ 2 ≤ Nat.card V :=
-- proof
  natCard_sq_le_of_isotropic hQ β hβ K hK


-- created on 2026-10-09
