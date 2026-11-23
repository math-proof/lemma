module

public import Mathlib
public import Theorem.MvPowerSeries.NegV2
public import Structure.MvFormalGroup_CartierModule
public import Def.MvFormalGroup_BasicV2
public import Def.FormalGroup_Weight
public import Instance.MvFormalGroup_EndRingV2

public noncomputable section

set_option autoImplicit false

noncomputable section

universe u

namespace MvFormalGroup

namespace WittLaw

open MvPolynomial

variable (p : ℕ) [hp : Fact p.Prime]

omit hp in
@[simp] public theorem weight_apply {idx : Type*} (c : idx → ℕ) (i : idx) (m : ℕ) :
    weight p c (i, m) = c i * p ^ m := rfl

omit hp in


public theorem isWeightedHomogeneous_rename_wittPolynomial {idx : Type*} (c : idx → ℕ) (i : idx)
    (n : ℕ) :
    IsWeightedHomogeneous (weight p c) (rename (Prod.mk i) (wittPolynomial p ℤ n))
      (c i * p ^ n) := by
  rw [wittPolynomial_eq_sum_C_mul_X_pow, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun j hj => ?_
  rw [map_mul, rename_C, map_pow, map_pow, rename_X]
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hX := (isWeightedHomogeneous_X (R := ℤ) (weight p c) (i, j)).pow (p ^ (n - j))
  have hdeg : (p ^ (n - j)) • weight p c (i, j) = c i * p ^ n := by
    rw [weight_apply, smul_eq_mul, ← mul_assoc, mul_comm (p ^ (n - j)), mul_assoc,
      ← pow_add, Nat.sub_add_cancel hj']
  rw [hdeg] at hX
  have := hX.C_mul ((p : ℤ) ^ j)
  rwa [map_pow] at this


public theorem isWeightedHomogeneous_wittStructureInt {idx : Type*} (c : idx → ℕ)
    (Φ : MvPolynomial idx ℤ) (k : ℕ)
    (hΦ : ∀ n, IsWeightedHomogeneous (weight p c)
      (bind₁ (fun i => rename (Prod.mk i) (wittPolynomial p ℤ n)) Φ) (k * p ^ n)) (n : ℕ) :
    IsWeightedHomogeneous (weight p c) (wittStructureInt p Φ n) (k * p ^ n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have key := wittStructureInt_prop p Φ n
    rw [← aeval_eq_bind₁, aeval_wittPolynomial, Finset.sum_range_succ, Nat.sub_self, pow_zero,
      pow_one] at key

    have hsum : IsWeightedHomogeneous (weight p c)
        (∑ i ∈ Finset.range n, (p : MvPolynomial (idx × ℕ) ℤ) ^ i *
          wittStructureInt p Φ i ^ p ^ (n - i)) (k * p ^ n) := by
      refine IsWeightedHomogeneous.sum _ _ _ fun i hi => ?_
      have hi' : i < n := Finset.mem_range.mp hi
      have h1 := (ih i hi').pow (p ^ (n - i))
      have hdeg : (p ^ (n - i)) • (k * p ^ i) = k * p ^ n := by
        rw [smul_eq_mul, mul_left_comm, ← pow_add, Nat.sub_add_cancel hi'.le]
      rw [hdeg] at h1
      have h2 := h1.C_mul ((p : ℤ) ^ i)
      rwa [map_pow, map_natCast] at h2
    intro d hd
    by_contra hne
    have hcoeff : (((p : MvPolynomial (idx × ℕ) ℤ) ^ n * wittStructureInt p Φ n).coeff d) = 0 := by
      have := congrArg (fun t : MvPolynomial (idx × ℕ) ℤ => t.coeff d) key
      have hsplit :
          ((∑ i ∈ Finset.range n, (p : MvPolynomial (idx × ℕ) ℤ) ^ i *
              wittStructureInt p Φ i ^ p ^ (n - i) +
            (p : MvPolynomial (idx × ℕ) ℤ) ^ n * wittStructureInt p Φ n).coeff d) =
          (∑ i ∈ Finset.range n, (p : MvPolynomial (idx × ℕ) ℤ) ^ i *
              wittStructureInt p Φ i ^ p ^ (n - i)).coeff d +
          ((p : MvPolynomial (idx × ℕ) ℤ) ^ n * wittStructureInt p Φ n).coeff d := by
        simp
      rw [hsplit] at this
      have hR : (bind₁ (fun i => rename (Prod.mk i) (wittPolynomial p ℤ n)) Φ).coeff d = 0 :=
        (hΦ n).coeff_eq_zero d hne
      have hS : (∑ i ∈ Finset.range n, (p : MvPolynomial (idx × ℕ) ℤ) ^ i *
          wittStructureInt p Φ i ^ p ^ (n - i)).coeff d = 0 := hsum.coeff_eq_zero d hne
      rw [hR, hS, zero_add] at this
      exact this
    have hC : (p : MvPolynomial (idx × ℕ) ℤ) ^ n = C ((p : ℤ) ^ n) := by
      rw [map_pow, map_natCast]
    rw [hC, coeff_C_mul] at hcoeff
    rcases mul_eq_zero.mp hcoeff with h | h
    · exact absurd h (pow_ne_zero _ (Int.natCast_ne_zero.mpr hp.out.ne_zero))
    · exact hd h


public theorem isWeightedHomogeneous_wittAdd (n : ℕ) :
    IsWeightedHomogeneous (weight p fun _ : Fin 2 => 1) (WittVector.wittAdd p n) (p ^ n) := by
  have h := isWeightedHomogeneous_wittStructureInt p (fun _ : Fin 2 => 1) (X 0 + X 1) 1
    (fun m => by
      rw [map_add, bind₁_X_right, bind₁_X_right, one_mul]
      have h0 := isWeightedHomogeneous_rename_wittPolynomial p (fun _ : Fin 2 => 1) 0 m
      have h1 := isWeightedHomogeneous_rename_wittPolynomial p (fun _ : Fin 2 => 1) 1 m
      rw [one_mul] at h0 h1
      exact h0.add h1) n
  rwa [one_mul] at h


public theorem isWeightedHomogeneous_wittMul (n : ℕ) :
    IsWeightedHomogeneous (weight p ![0, 1]) (WittVector.wittMul p n) (p ^ n) := by
  have h := isWeightedHomogeneous_wittStructureInt p ![0, 1] (X 0 * X 1) 1
    (fun m => by
      rw [map_mul, bind₁_X_right, bind₁_X_right, one_mul]
      have h0 := isWeightedHomogeneous_rename_wittPolynomial p ![0, 1] 0 m
      have h1 := isWeightedHomogeneous_rename_wittPolynomial p ![0, 1] 1 m
      simp only [Matrix.cons_val_zero, zero_mul, Matrix.cons_val_one, one_mul] at h0 h1
      have := h0.mul h1
      rwa [zero_add] at this) n
  rwa [one_mul] at h

variable (R : Type u) [CommRing R]


public theorem constantCoeff_addFam (n : ℕ) : MvPowerSeries.constantCoeff (addFam p R n) = 0 := by
  rw [addFam, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe,
    coeff_map, ← constantCoeff_eq, WittVector.constantCoeff_wittAdd, map_zero]


public theorem weight_eq_of_coeff_addFam_ne_zero {n : ℕ} {d : Fin 2 × ℕ →₀ ℕ}
    (h : MvPowerSeries.coeff d (addFam p R n) ≠ 0) :
    Finsupp.weight (weight p fun _ : Fin 2 => 1) d = p ^ n := by
  rw [addFam, MvPolynomial.coeff_coe, coeff_map] at h
  have h' : (WittVector.wittAdd p n).coeff d ≠ 0 := fun h0 => h (by rw [h0, map_zero])
  exact isWeightedHomogeneous_wittAdd p n h'


public theorem hasSubst_addFam : MvPowerSeries.HasSubst (addFam p R) := by
  refine ⟨fun n => by rw [constantCoeff_addFam]; exact IsNilpotent.zero, fun d => ?_⟩
  · refine (Set.finite_lt_nat (Finsupp.weight (weight p fun _ : Fin 2 => 1) d)).subset ?_
    intro n hn
    have hw := weight_eq_of_coeff_addFam_ne_zero p R hn
    show n < Finsupp.weight (weight p fun _ : Fin 2 => 1) d
    rw [hw]
    exact Nat.lt_pow_self hp.out.one_lt

variable {R}

omit hp in

@[simp] public theorem blk_apply (i : Fin 2) (m : ℕ) : blk (R := R) i m = MvPowerSeries.X (i, m) := rfl

omit hp in

public theorem constantCoeff_blk (i : Fin 2) (m : ℕ) :
    MvPowerSeries.constantCoeff (blk (R := R) i m) = 0 :=
  MvPowerSeries.constantCoeff_X _

omit hp in

public theorem hasSubst_blk (i : Fin 2) : MvPowerSeries.HasSubst (blk (R := R) i) :=
  MvPowerSeries.HasSubst.X_comp (Function.Embedding.sectR i ℕ)

omit hp in


public theorem subst_blk_eq_rename (i : Fin 2) (f : MvPowerSeries ℕ R) :
    MvPowerSeries.subst (blk i) f = MvPowerSeries.rename (Function.Embedding.sectR i ℕ) f :=
  (MvPowerSeries.rename_eq_subst (Function.Embedding.sectR i ℕ) f).symm

end WittLaw

open MvPowerSeries WittLaw

variable {p : ℕ} [hp : Fact p.Prime] {d d' d'' : ℕ} {R : Type u} [CommRing R]


namespace CartierModule

variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} {Φ'' : MvFormalGroup d'' R}


@[ext] public theorem ext {f g : CartierModule p Φ} (h : f.toPowerSeries = g.toPowerSeries) : f = g := by
  cases f; cases g; cases h; rfl


public theorem hasSubst_toPowerSeries (f : CartierModule p Φ) : HasSubst f.toPowerSeries :=
  hasSubst_of_constantCoeff_zero f.constantCoeff_eq_zero


end CartierModule

namespace WittLaw

variable (p)


variable {p}

omit hp in

@[simp] public theorem pairFam_apply (u : ℕ → MvPowerSeries ℕ R) (i : Fin 2) (m : ℕ) :
    pairFam u (i, m) = subst (blk i) (u m) := rfl

omit hp in

public theorem constantCoeff_pairFam {u : ℕ → MvPowerSeries ℕ R} (hu : ∀ n, (u n).constantCoeff = 0)
    (im : Fin 2 × ℕ) : (pairFam u im).constantCoeff = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_blk im.1) (constantCoeff_blk im.1) (hu im.2)

omit hp in


public theorem exists_coeff_ne_zero_of_coeff_subst_blk_ne_zero (i : Fin 2) (f : MvPowerSeries ℕ R)
    {e : Fin 2 × ℕ →₀ ℕ} (h : coeff e (subst (blk (R := R) i) f) ≠ 0) :
    ∃ x : ℕ →₀ ℕ, Finsupp.mapDomain (Prod.mk i) x = e ∧ coeff x f ≠ 0 := by
  rw [subst_blk_eq_rename, coeff_rename] at h
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨x, ?_, hne⟩
  simpa using hx

omit hp in


public theorem hasSubst_pairFam {u : ℕ → MvPowerSeries ℕ R} (hu : HasSubst u)
    (hu0 : ∀ n, (u n).constantCoeff = 0) : HasSubst (pairFam u) := by
  refine ⟨fun im => by rw [constantCoeff_pairFam hu0]; exact IsNilpotent.zero, fun e => ?_⟩
  have hfin : ∀ i : Fin 2, {m : ℕ | coeff e (subst (blk (R := R) i) (u m)) ≠ 0}.Finite := by
    intro i
    by_cases hx : ∃ x : ℕ →₀ ℕ, Finsupp.mapDomain (Prod.mk i) x = e
    · obtain ⟨x, rfl⟩ := hx
      refine (hu.coeff_zero x).subset fun m hm => ?_
      obtain ⟨y, hy, hne⟩ := exists_coeff_ne_zero_of_coeff_subst_blk_ne_zero i (u m) hm
      have hyx : y = x := Finsupp.mapDomain_injective (Prod.mk_right_injective i) hy
      rw [hyx] at hne
      exact hne
    · convert Set.finite_empty
      ext m
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      by_contra hm
      obtain ⟨y, hy, -⟩ := exists_coeff_ne_zero_of_coeff_subst_blk_ne_zero i (u m) hm
      exact hx ⟨y, hy⟩
  have hsub : {im : Fin 2 × ℕ | coeff e (pairFam u im) ≠ 0} ⊆
      ⋃ i : Fin 2, Prod.mk i '' {m : ℕ | coeff e (subst (blk (R := R) i) (u m)) ≠ 0} := by
    rintro ⟨i, m⟩ him
    exact Set.mem_iUnion.mpr ⟨i, m, him, rfl⟩
  exact (Set.finite_iUnion fun i => (hfin i).image _).subset hsub

omit hp in


public theorem subst_pairFam_subst_blk {u : ℕ → MvPowerSeries ℕ R} (hu : HasSubst u)
    (hu0 : ∀ n, (u n).constantCoeff = 0) (i : Fin 2) (f : MvPowerSeries ℕ R) :
    subst (pairFam u) (subst (blk (R := R) i) f) = subst (blk (R := R) i) (subst u f) := by
  rw [subst_comp_subst_apply (hasSubst_blk i) (hasSubst_pairFam hu hu0),
    subst_comp_subst_apply hu (hasSubst_blk i)]
  congr 1
  funext m
  show subst (pairFam u) (X (i, m)) = subst (blk i) (u m)
  rw [subst_X (hasSubst_pairFam hu hu0)]
  rfl

variable (R)


public theorem aeval_verschiebung_wittAdd (n : ℕ) :
    MvPolynomial.aeval (fun im : Fin 2 × ℕ =>
        (Nat.casesOn im.2 0 fun m => MvPolynomial.X (im.1, m) : MvPolynomial (Fin 2 × ℕ) ℤ))
      (WittVector.wittAdd p n) =
      Nat.casesOn n 0 fun m => WittVector.wittAdd p m := by

  let A := MvPolynomial (Fin 2 × ℕ) ℤ
  let x : WittVector p A := WittVector.mk p fun m => MvPolynomial.X (0, m)
  let y : WittVector p A := WittVector.mk p fun m => MvPolynomial.X (1, m)
  have key := congrArg (fun z : WittVector p A => z.coeff n)
    (WittVector.verschiebung.map_add x y).symm
  have hval : (fun im : Fin 2 × ℕ =>
      (Nat.casesOn im.2 0 fun m => MvPolynomial.X (im.1, m) : A)) =
      Function.uncurry ![(WittVector.verschiebung x).coeff, (WittVector.verschiebung y).coeff] := by
    funext ⟨i, m⟩
    fin_cases i <;> cases m <;> rfl
  rw [hval]
  change WittVector.peval (WittVector.wittAdd p n)
      ![(WittVector.verschiebung x).coeff, (WittVector.verschiebung y).coeff] = _
  rw [← WittVector.add_coeff, key]
  cases n with
  | zero => exact WittVector.verschiebung_coeff_zero _
  | succ m =>
    rw [WittVector.verschiebung_coeff_succ, WittVector.add_coeff]
    show MvPolynomial.aeval (Function.uncurry ![x.coeff, y.coeff]) (WittVector.wittAdd p m) = _
    have hid : Function.uncurry ![x.coeff, y.coeff] = (MvPolynomial.X : Fin 2 × ℕ → A) := by
      funext ⟨i, k⟩
      fin_cases i <;> rfl
    rw [hid, MvPolynomial.aeval_X_left_apply]


public theorem subst_coe_addFam {τ : Type*} (g : Fin 2 × ℕ → MvPolynomial τ ℤ) (n : ℕ) :
    subst (fun im => ((MvPolynomial.map (Int.castRingHom R) (g im) : MvPolynomial τ R) :
      MvPowerSeries τ R)) (addFam p R n) =
      ((MvPolynomial.map (Int.castRingHom R) (MvPolynomial.aeval g (WittVector.wittAdd p n)) :
        MvPolynomial τ R) : MvPowerSeries τ R) := by
  rw [addFam, subst_coe]
  set G : Fin 2 × ℕ → MvPowerSeries τ R := fun im =>
    ((MvPolynomial.map (Int.castRingHom R) (g im) : MvPolynomial τ R) : MvPowerSeries τ R)
  let ψ₁ : MvPolynomial (Fin 2 × ℕ) ℤ →+* MvPowerSeries τ R :=
    (MvPolynomial.aeval G).toRingHom.comp (MvPolynomial.map (Int.castRingHom R))
  let ψ₂ : MvPolynomial (Fin 2 × ℕ) ℤ →+* MvPowerSeries τ R :=
    (MvPolynomial.coeToMvPowerSeries.ringHom (σ := τ) (R := R)).comp
      ((MvPolynomial.map (Int.castRingHom R)).comp (MvPolynomial.aeval g).toRingHom)
  have hψ : ψ₁ = ψ₂ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun im => ?_)
    · have h1 := RingHom.ext_int (ψ₁.comp (MvPolynomial.C : ℤ →+* MvPolynomial (Fin 2 × ℕ) ℤ))
        (ψ₂.comp (MvPolynomial.C : ℤ →+* MvPolynomial (Fin 2 × ℕ) ℤ))
      exact RingHom.congr_fun h1 r
    · simp [ψ₁, ψ₂, G]
  exact RingHom.congr_fun hψ (WittVector.wittAdd p n)


public theorem expand_map_wittAdd [CharP R p] (n : ℕ) :
    MvPolynomial.expand p (MvPolynomial.map (Int.castRingHom R) (WittVector.wittAdd p n)) =
      MvPolynomial.map (Int.castRingHom R) (WittVector.wittAdd p n) ^ p := by
  haveI : ExpChar R p := ExpChar.prime hp.out
  rw [← MvPolynomial.map_frobenius_expand p, MvPolynomial.map_expand, MvPolynomial.map_map,
    show (frobenius R p).comp (Int.castRingHom R) = Int.castRingHom R from RingHom.ext_int _ _]


end WittLaw

namespace CartierModule

variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} {Φ'' : MvFormalGroup d'' R}


public theorem _root_.MvFormalGroup.Hom.subst_subst_elim {τ : Type*} {F : MvFormalGroup d R}
    {G : MvFormalGroup d' R} (φ : F.Hom G) {a b : Fin d → MvPowerSeries τ R}
    (ha : ∀ j, (a j).constantCoeff = 0) (hb : ∀ j, (b j).constantCoeff = 0) (i : Fin d') :
    subst (fun j => subst (Sum.elim a b) (F.toPowerSeries j)) (φ.toPowerSeries i) =
      subst (Sum.elim (fun j => subst a (φ.toPowerSeries j)) fun j => subst b (φ.toPowerSeries j))
        (G.toPowerSeries i) := by
  have hab : HasSubst (Sum.elim a b) := hasSubst_elim ha hb
  have hXl : HasSubst (fun l : Fin d => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
  have hXr : HasSubst (fun l : Fin d => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
  have hLR : HasSubst (Sum.elim
      (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) R))
        (φ.toPowerSeries j))
      fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) R))
        (φ.toPowerSeries j)) :=
    hasSubst_elim
      (fun j => constantCoeff_subst_eq_zero hXl (fun l => constantCoeff_X _)
        (φ.constantCoeff_eq_zero j))
      fun j => constantCoeff_subst_eq_zero hXr (fun l => constantCoeff_X _)
        (φ.constantCoeff_eq_zero j)
  have key := congrArg (subst (Sum.elim a b)) (φ.subst_eq i)
  rw [subst_comp_subst_apply F.hasSubst_toPowerSeries hab, subst_comp_subst_apply hLR hab] at key
  rw [key]
  congr 1
  funext s
  rcases s with j | j
  · show subst (Sum.elim a b) (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) R))
        (φ.toPowerSeries j)) = subst a (φ.toPowerSeries j)
    rw [subst_comp_subst_apply hXl hab]
    congr 1
    funext l
    exact subst_X hab (Sum.inl l)
  · show subst (Sum.elim a b) (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) R))
        (φ.toPowerSeries j)) = subst b (φ.toPowerSeries j)
    rw [subst_comp_subst_apply hXr hab]
    congr 1
    funext l
    exact subst_X hab (Sum.inr l)


end CartierModule

namespace WittLaw


public theorem isWeightedHomogeneous_wittNSMul (n k : ℕ) :
    MvPolynomial.IsWeightedHomogeneous (weight p fun _ : Fin 1 => 1) (WittVector.wittNSMul p n k)
      (p ^ k) := by
  have h := isWeightedHomogeneous_wittStructureInt p (fun _ : Fin 1 => 1)
    (n • MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) ℤ) 1
    (fun m => by
      rw [map_nsmul, MvPolynomial.bind₁_X_right, one_mul, nsmul_eq_mul, ← map_natCast MvPolynomial.C]
      have h0 := isWeightedHomogeneous_rename_wittPolynomial p (fun _ : Fin 1 => 1) 0 m
      rw [one_mul] at h0
      exact h0.C_mul _) k
  rwa [one_mul] at h


omit hp in


public theorem peval_tautological (φ : MvPolynomial (Fin 1 × ℕ) ℤ) :
    WittVector.peval φ ![(WittVector.mk p fun m => (MvPolynomial.X (0, m) :
      MvPolynomial (Fin 1 × ℕ) ℤ)).coeff] = φ := by
  have hid : Function.uncurry ![(WittVector.mk p fun m => (MvPolynomial.X (0, m) :
      MvPolynomial (Fin 1 × ℕ) ℤ)).coeff] = (MvPolynomial.X : Fin 1 × ℕ → _) := by
    funext ⟨i, m⟩
    fin_cases i; rfl
  show MvPolynomial.aeval _ φ = φ
  rw [hid, MvPolynomial.aeval_X_left_apply]


public theorem wittNSMul_zero (k : ℕ) : WittVector.wittNSMul p 0 k = 0 := by
  let x : WittVector p (MvPolynomial (Fin 1 × ℕ) ℤ) := WittVector.mk p fun m => MvPolynomial.X (0, m)
  have h := WittVector.nsmul_coeff 0 x k
  rw [zero_nsmul, WittVector.zero_coeff, peval_tautological] at h
  exact h.symm


public theorem aeval_wittNSMul_wittAdd (n k : ℕ) :
    MvPolynomial.aeval (fun im : Fin 2 × ℕ =>
        (Fin.cases (WittVector.wittNSMul p n im.2) (fun _ => MvPolynomial.X (0, im.2)) im.1 :
          MvPolynomial (Fin 1 × ℕ) ℤ)) (WittVector.wittAdd p k) =
      WittVector.wittNSMul p (n + 1) k := by
  let x : WittVector p (MvPolynomial (Fin 1 × ℕ) ℤ) := WittVector.mk p fun m => MvPolynomial.X (0, m)
  have h := WittVector.nsmul_coeff (n + 1) x k
  rw [peval_tautological, succ_nsmul, WittVector.add_coeff] at h
  have hval : (fun im : Fin 2 × ℕ =>
      (Fin.cases (WittVector.wittNSMul p n im.2) (fun _ => MvPolynomial.X (0, im.2)) im.1 :
        MvPolynomial (Fin 1 × ℕ) ℤ)) = Function.uncurry ![(n • x).coeff, x.coeff] := by
    funext ⟨i, m⟩
    refine Fin.cases ?_ (fun l => ?_) i
    · show WittVector.wittNSMul p n m = (n • x).coeff m
      rw [WittVector.nsmul_coeff, peval_tautological]
    · fin_cases l; rfl
  rw [hval]
  exact h


public theorem aeval_X_eq_map {σ : Type*} (S : Type*) [CommRing S] (φ : MvPolynomial σ ℤ) :
    MvPolynomial.aeval (MvPolynomial.X : σ → MvPolynomial σ S) φ =
      MvPolynomial.map (Int.castRingHom S) φ := by
  refine RingHom.congr_fun (?_ :
    (MvPolynomial.aeval (MvPolynomial.X : σ → MvPolynomial σ S)).toRingHom =
      MvPolynomial.map (Int.castRingHom S)) φ
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · exact RingHom.congr_fun (RingHom.ext_int
      ((MvPolynomial.aeval (MvPolynomial.X : σ → MvPolynomial σ S)).toRingHom.comp
        (MvPolynomial.C : ℤ →+* MvPolynomial σ ℤ))
      ((MvPolynomial.map (Int.castRingHom S)).comp (MvPolynomial.C : ℤ →+* MvPolynomial σ ℤ))) r
  · simp


public theorem map_wittNSMul_self (k : ℕ) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) (WittVector.wittNSMul p p k) =
      Nat.casesOn k 0 fun m => MvPolynomial.X (0, m) ^ p := by
  let A := MvPolynomial (Fin 1 × ℕ) (ZMod p)
  let x : WittVector p A := WittVector.mk p fun m => MvPolynomial.X (0, m)
  have h := WittVector.nsmul_coeff p x k
  have hid : Function.uncurry ![x.coeff] = (MvPolynomial.X : Fin 1 × ℕ → A) := by
    funext ⟨i, m⟩
    fin_cases i; rfl
  have hev : WittVector.peval (WittVector.wittNSMul p p k) ![x.coeff] =
      MvPolynomial.map (Int.castRingHom (ZMod p)) (WittVector.wittNSMul p p k) := by
    show MvPolynomial.aeval _ _ = _
    rw [hid]
    exact aeval_X_eq_map (ZMod p) _
  rw [← hev, ← h, nsmul_eq_mul, mul_comm]
  cases k with
  | zero => exact WittVector.mul_charP_coeff_zero x
  | succ m => exact WittVector.mul_charP_coeff_succ x m

omit hp in


public theorem hasSubst_finCases {τ : Type*} {u₀ u₁ : ℕ → MvPowerSeries τ R} (h₀ : HasSubst u₀)
    (h₁ : HasSubst u₁) :
    HasSubst (fun im : Fin 2 × ℕ => (Fin.cases (u₀ im.2) (fun _ => u₁ im.2) im.1 : MvPowerSeries τ R)) := by
  refine ⟨fun ⟨i, m⟩ => Fin.cases (h₀.const_coeff m) (fun _ => h₁.const_coeff m) i, fun e => ?_⟩
  refine (((h₀.coeff_zero e).image (Prod.mk 0)).union ((h₁.coeff_zero e).image (Prod.mk 1))).subset ?_
  rintro ⟨i, m⟩ him
  revert him
  refine Fin.cases (fun him => Or.inl ⟨m, him, rfl⟩) (fun l him => Or.inr ⟨m, him, ?_⟩) i
  fin_cases l; rfl

end WittLaw

end MvFormalGroup

end
