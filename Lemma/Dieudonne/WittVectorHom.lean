import Mathlib
import Lemma.Dieudonne.DatumAndHonda
import Instance.Dieudonne_WittVectorHom
import Abbrev.Dieudonne_WittVectorHom

set_option autoImplicit false

open Function

universe u v w

namespace Deformation

namespace TruncWitt

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}
variable {R : Type u} {S : Type v} {T : Type w} [CommRing R] [CommRing S] [CommRing T]

noncomputable def map (f : R →+* S) : TruncatedWittVector p n R →+* TruncatedWittVector p n S :=
  RingHom.liftOfRightInverse (WittVector.truncate n) TruncatedWittVector.out
    TruncatedWittVector.truncateFun_out
    ⟨(WittVector.truncate n).comp (WittVector.map f), fun x hx => by
      rw [WittVector.mem_ker_truncate] at hx
      simp only [RingHom.mem_ker, RingHom.comp_apply, TruncatedWittVector.ext_iff,
        WittVector.coeff_truncate, WittVector.map_coeff, TruncatedWittVector.coeff_zero]
      exact fun i => by rw [hx i i.isLt]; exact map_zero f⟩

@[simp] theorem map_truncate (f : R →+* S) (x : WittVector p R) :
    map f (WittVector.truncate n x) = WittVector.truncate n (WittVector.map f x) :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ _

@[simp] theorem coeff_map (f : R →+* S) (x : TruncatedWittVector p n R) (i : Fin n) :
    (map f x).coeff i = f (x.coeff i) := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  simp [WittVector.coeff_truncate, WittVector.map_coeff]

theorem map_map (f : R →+* S) (g : S →+* T) (x : TruncatedWittVector p n R) :
    map g (map f x) = map (g.comp f) x :=
  TruncatedWittVector.ext fun i => by simp only [coeff_map, RingHom.comp_apply]

theorem map_comp (f : R →+* S) (g : S →+* T) :
    (map (p := p) (n := n) g).comp (map f) = map (g.comp f) :=
  RingHom.ext fun x => map_map f g x

@[simp] theorem map_id (x : TruncatedWittVector p n R) : map (RingHom.id R) x = x :=
  TruncatedWittVector.ext fun i => by simp only [coeff_map, RingHom.id_apply]

theorem map_injective {f : R →+* S} (hf : Injective f) :
    Injective (map (p := p) (n := n) f) := fun x y h =>
  TruncatedWittVector.ext fun i => hf (by
    have := congrArg (TruncatedWittVector.coeff i) h
    simpa only [coeff_map] using this)

theorem map_congr {f g : R →+* S} {x : TruncatedWittVector p n R}
    (h : ∀ i, f (x.coeff i) = g (x.coeff i)) : map f x = map g x :=
  TruncatedWittVector.ext fun i => by simp only [coeff_map, h i]

noncomputable def verschiebung : TruncatedWittVector p n R →+ TruncatedWittVector p n R :=
  AddMonoidHom.liftOfRightInverse (WittVector.truncate n).toAddMonoidHom TruncatedWittVector.out
    (fun x => TruncatedWittVector.truncateFun_out x)
    ⟨(WittVector.truncate n).toAddMonoidHom.comp WittVector.verschiebung, fun x hx => by
      change (WittVector.truncate n) x = 0 at hx
      rw [← RingHom.mem_ker, WittVector.mem_ker_truncate] at hx
      change (WittVector.truncate n) (WittVector.verschiebung x) = 0
      ext ⟨i, hi⟩
      simp only [WittVector.coeff_truncate, TruncatedWittVector.coeff_zero]
      cases i with
      | zero => exact WittVector.verschiebung_coeff_zero x
      | succ j =>
        rw [WittVector.verschiebung_coeff_succ]
        exact hx j (Nat.lt_of_succ_lt hi)⟩

@[simp] theorem verschiebung_truncate (x : WittVector p R) :
    verschiebung (WittVector.truncate n x) = WittVector.truncate n (WittVector.verschiebung x) :=
  AddMonoidHom.liftOfRightInverse_comp_apply _ _
    (fun x => TruncatedWittVector.truncateFun_out x) _ _

theorem coeff_verschiebung_zero (x : TruncatedWittVector p (n + 1) R) :
    (verschiebung x).coeff 0 = 0 := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p (n + 1) R x
  rw [verschiebung_truncate, WittVector.coeff_truncate]
  exact WittVector.verschiebung_coeff_zero x

theorem coeff_verschiebung_succ (x : TruncatedWittVector p n R) (i : ℕ) (hi : i + 1 < n) :
    (verschiebung x).coeff ⟨i + 1, hi⟩ = x.coeff ⟨i, Nat.lt_of_succ_lt hi⟩ := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  rw [verschiebung_truncate, WittVector.coeff_truncate, WittVector.coeff_truncate]
  exact WittVector.verschiebung_coeff_succ x i

theorem map_verschiebung (f : R →+* S) (x : TruncatedWittVector p n R) :
    map f (verschiebung x) = verschiebung (map f x) := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  rw [verschiebung_truncate, map_truncate, map_truncate, verschiebung_truncate,
    WittVector.map_verschiebung]

def frobeniusFun (x : TruncatedWittVector p n R) : TruncatedWittVector p n R :=
  TruncatedWittVector.mk p fun i => x.coeff i ^ p

omit hp in
@[simp] theorem coeff_frobeniusFun (x : TruncatedWittVector p n R) (i : Fin n) :
    (frobeniusFun x).coeff i = x.coeff i ^ p :=
  TruncatedWittVector.coeff_mk _ _

theorem map_frobeniusFun (f : R →+* S) (x : TruncatedWittVector p n R) :
    map f (frobeniusFun x) = frobeniusFun (map f x) :=
  TruncatedWittVector.ext fun i => by simp only [coeff_map, coeff_frobeniusFun, map_pow]

theorem frobeniusFun_verschiebung (x : TruncatedWittVector p n R) :
    frobeniusFun (verschiebung x) = verschiebung (frobeniusFun x) := by
  refine TruncatedWittVector.ext fun ⟨i, hi⟩ => ?_
  cases n with
  | zero => exact absurd hi (Nat.not_lt_zero _)
  | succ m =>
    cases i with
    | zero =>
      change (frobeniusFun (verschiebung x)).coeff 0 = (verschiebung (frobeniusFun x)).coeff 0
      rw [coeff_frobeniusFun, coeff_verschiebung_zero, coeff_verschiebung_zero,
        zero_pow hp.out.ne_zero]
    | succ j =>
      rw [coeff_frobeniusFun, coeff_verschiebung_succ _ _ hi, coeff_verschiebung_succ _ _ hi,
        coeff_frobeniusFun]

theorem subsingleton_or_charP (hR : (p : R) = 0) : Subsingleton R ∨ CharP R p := by
  rcases subsingleton_or_nontrivial R with h | h
  · exact Or.inl h
  · refine Or.inr ((CharP.charP_iff_prime_eq_zero hp.out).2 hR)

theorem frobeniusFun_truncate [CharP R p] (x : WittVector p R) :
    frobeniusFun (WittVector.truncate n x) = WittVector.truncate n (WittVector.frobenius x) :=
  TruncatedWittVector.ext fun i => by
    simp only [coeff_frobeniusFun, WittVector.coeff_truncate, WittVector.coeff_frobenius_charP]

theorem frobeniusFun_add (hR : (p : R) = 0) (x y : TruncatedWittVector p n R) :
    frobeniusFun (x + y) = frobeniusFun x + frobeniusFun y := by
  rcases subsingleton_or_charP hR with h | h
  · exact Subsingleton.elim _ _
  · obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
    obtain ⟨y, rfl⟩ := WittVector.truncate_surjective p n R y
    rw [← map_add, frobeniusFun_truncate, frobeniusFun_truncate, frobeniusFun_truncate,
      map_add, map_add]

theorem frobeniusFun_zero : frobeniusFun (0 : TruncatedWittVector p n R) = 0 :=
  TruncatedWittVector.ext fun i => by
    simp only [coeff_frobeniusFun, TruncatedWittVector.coeff_zero, zero_pow hp.out.ne_zero]

theorem verschiebung_frobeniusFun (hR : (p : R) = 0) (x : TruncatedWittVector p n R) :
    verschiebung (frobeniusFun x) = (p : ℤ) • x := by
  rcases subsingleton_or_charP hR with h | h
  · exact Subsingleton.elim _ _
  · obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
    rw [frobeniusFun_truncate, verschiebung_truncate, WittVector.verschiebung_frobenius,
      ← nsmul_eq_mul', map_nsmul, natCast_zsmul]

theorem frobeniusFun_verschiebung_eq_smul (hR : (p : R) = 0) (x : TruncatedWittVector p n R) :
    frobeniusFun (verschiebung x) = (p : ℤ) • x := by
  rw [frobeniusFun_verschiebung, verschiebung_frobeniusFun hR]

noncomputable def shift : TruncatedWittVector p n R →+ TruncatedWittVector p (n + 1) R :=
  AddMonoidHom.liftOfRightInverse (WittVector.truncate n).toAddMonoidHom TruncatedWittVector.out
    (fun x => TruncatedWittVector.truncateFun_out x)
    ⟨(WittVector.truncate (n + 1)).toAddMonoidHom.comp WittVector.verschiebung, fun x hx => by
      change (WittVector.truncate n) x = 0 at hx
      rw [← RingHom.mem_ker, WittVector.mem_ker_truncate] at hx
      change (WittVector.truncate (n + 1)) (WittVector.verschiebung x) = 0
      ext ⟨i, hi⟩
      simp only [WittVector.coeff_truncate, TruncatedWittVector.coeff_zero]
      cases i with
      | zero => exact WittVector.verschiebung_coeff_zero x
      | succ j =>
        rw [WittVector.verschiebung_coeff_succ]
        exact hx j (Nat.lt_of_succ_lt_succ hi)⟩

@[simp] theorem shift_truncate (x : WittVector p R) :
    shift (WittVector.truncate n x) = WittVector.truncate (n + 1) (WittVector.verschiebung x) :=
  AddMonoidHom.liftOfRightInverse_comp_apply _ _
    (fun x => TruncatedWittVector.truncateFun_out x) _ _

theorem coeff_shift_zero (x : TruncatedWittVector p n R) : (shift x).coeff 0 = 0 := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  rw [shift_truncate, WittVector.coeff_truncate]
  exact WittVector.verschiebung_coeff_zero x

theorem coeff_shift_succ (x : TruncatedWittVector p n R) (i : Fin n) :
    (shift x).coeff i.succ = x.coeff i := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  rw [shift_truncate, WittVector.coeff_truncate, WittVector.coeff_truncate]
  exact WittVector.verschiebung_coeff_succ x i

theorem shift_injective : Injective (shift (p := p) (n := n) (R := R)) := fun x y h =>
  TruncatedWittVector.ext fun i => by
    rw [← coeff_shift_succ x i, ← coeff_shift_succ y i, h]

theorem map_shift (f : R →+* S) (x : TruncatedWittVector p n R) :
    map f (shift x) = shift (map f x) := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  rw [shift_truncate, map_truncate, map_truncate, shift_truncate, WittVector.map_verschiebung]

theorem truncate_shift (x : TruncatedWittVector p n R) :
    TruncatedWittVector.truncate (Nat.le_succ n) (shift x) = verschiebung x := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  rw [shift_truncate, TruncatedWittVector.truncate_wittVector_truncate, verschiebung_truncate]

theorem shift_truncate_succ (y : TruncatedWittVector p (n + 1) R) :
    shift (TruncatedWittVector.truncate (Nat.le_succ n) y) = verschiebung y := by
  obtain ⟨y, rfl⟩ := WittVector.truncate_surjective p (n + 1) R y
  rw [TruncatedWittVector.truncate_wittVector_truncate, shift_truncate, verschiebung_truncate]

theorem frobeniusFun_shift (x : TruncatedWittVector p n R) :
    frobeniusFun (shift x) = shift (frobeniusFun x) := by
  refine TruncatedWittVector.ext fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [coeff_frobeniusFun, coeff_shift_zero, coeff_shift_zero, zero_pow hp.out.ne_zero]
  · rw [coeff_frobeniusFun, coeff_shift_succ, coeff_shift_succ, coeff_frobeniusFun]

theorem map_truncateLE {m : ℕ} (hm : n ≤ m) (f : R →+* S) (x : TruncatedWittVector p m R) :
    map f (TruncatedWittVector.truncate hm x) = TruncatedWittVector.truncate hm (map f x) :=
  TruncatedWittVector.ext fun i => by
    simp only [coeff_map, TruncatedWittVector.coeff_truncate]

theorem verschiebung_truncateLE {m : ℕ} (hm : n ≤ m) (x : TruncatedWittVector p m R) :
    verschiebung (TruncatedWittVector.truncate hm x) =
      TruncatedWittVector.truncate hm (verschiebung x) := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p m R x
  rw [TruncatedWittVector.truncate_wittVector_truncate, verschiebung_truncate,
    verschiebung_truncate, TruncatedWittVector.truncate_wittVector_truncate]

theorem frobeniusFun_truncateLE {m : ℕ} (hm : n ≤ m) (x : TruncatedWittVector p m R) :
    frobeniusFun (TruncatedWittVector.truncate hm x) =
      TruncatedWittVector.truncate hm (frobeniusFun x) :=
  TruncatedWittVector.ext fun i => by
    simp only [coeff_frobeniusFun, TruncatedWittVector.coeff_truncate]

end TruncWitt

section WittHom

variable (R : Type u) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (n : ℕ)
variable (A : Type v) [CommRing A] [Bialgebra R A]

open TruncWitt

noncomputable def wittHom : AddSubgroup (TruncatedWittVector p n A) where
  carrier := {x | map (comulRingHom R A) x =
    map (Algebra.TensorProduct.includeLeft : A →ₐ[R] TensorProduct R A A).toRingHom x +
    map (Algebra.TensorProduct.includeRight : A →ₐ[R] TensorProduct R A A).toRingHom x}
  zero_mem' := by simp
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq, map_add] at hx hy ⊢
    rw [hx, hy]; abel
  neg_mem' {x} hx := by
    simp only [Set.mem_setOf_eq, map_neg] at hx ⊢
    rw [hx]; abel

variable {R p n A}

theorem mem_wittHom_iff (x : TruncatedWittVector p n A) :
    x ∈ wittHom R p n A ↔ map (comulRingHom R A) x =
      map (Algebra.TensorProduct.includeLeft : A →ₐ[R] TensorProduct R A A).toRingHom x +
      map (Algebra.TensorProduct.includeRight : A →ₐ[R] TensorProduct R A A).toRingHom x :=
  Iff.rfl

theorem map_convMul_of_mem_wittHom {T : Type w} [CommRing T] [Algebra R T]
    {x : TruncatedWittVector p n A} (hx : x ∈ wittHom R p n A)
    (f g : WithConv (A →ₐ[R] T)) :
    map (f * g).ofConv.toRingHom x = map f.ofConv.toRingHom x + map g.ofConv.toRingHom x := by
  have key : (f * g).ofConv.toRingHom =
      (Algebra.TensorProduct.lift f.ofConv g.ofConv (fun _ _ => Commute.all _ _)).toRingHom.comp
        (comulRingHom R A) := by
    refine RingHom.ext fun c => ?_
    change (f * g) c = _
    rw [AlgHom.convMul_apply]
    rfl
  rw [key, ← map_map, (mem_wittHom_iff x).1 hx, map_add, map_map, map_map]
  congr 1
  · exact congrArg (fun h : A →+* T => map h x)
      (congrArg AlgHom.toRingHom (Algebra.TensorProduct.lift_comp_includeLeft f.ofConv g.ofConv
        (fun _ _ => Commute.all _ _)))
  · exact congrArg (fun h : A →+* T => map h x)
      (congrArg AlgHom.toRingHom (Algebra.TensorProduct.lift_comp_includeRight f.ofConv g.ofConv
        (fun _ _ => Commute.all _ _)))

theorem map_counit_of_mem_wittHom {x : TruncatedWittVector p n A} (hx : x ∈ wittHom R p n A) :
    map (Bialgebra.counitAlgHom R A).toRingHom x = 0 := by

  have h := map_convMul_of_mem_wittHom (T := A) hx 1 (WithConv.toConv (AlgHom.id R A))
  rw [one_mul] at h
  have h1 : map (1 : WithConv (A →ₐ[R] A)).ofConv.toRingHom x = 0 :=
    (add_right_cancel ((zero_add _).trans h)).symm

  have hfac : (1 : WithConv (A →ₐ[R] A)).ofConv.toRingHom =
      (algebraMap R A).comp (Bialgebra.counitAlgHom R A).toRingHom := by
    refine RingHom.ext fun c => ?_
    simp [AlgHom.convOne_apply]
  rw [hfac, ← map_map] at h1
  have hinj : Injective (map (p := p) (n := n) (algebraMap R A)) :=
    map_injective fun r s hrs => by
      simpa using congrArg (Coalgebra.counit (R := R) (A := A)) hrs
  exact hinj (by rw [h1, map_zero])

theorem counit_coeff_of_mem_wittHom {x : TruncatedWittVector p n A} (hx : x ∈ wittHom R p n A)
    (i : Fin n) : Coalgebra.counit (R := R) (x.coeff i) = 0 := by
  have := congrArg (TruncatedWittVector.coeff i) (map_counit_of_mem_wittHom hx)
  simp only [coeff_map, TruncatedWittVector.coeff_zero] at this
  exact this

section Map

variable {B : Type w} [CommRing B] [Bialgebra R B]

theorem map_mem_wittHom (φ : A →ₐc[R] B) {x : TruncatedWittVector p n A}
    (hx : x ∈ wittHom R p n A) : map (φ : A →ₐ[R] B).toRingHom x ∈ wittHom R p n B := by
  rw [mem_wittHom_iff] at hx ⊢

  have hΔ : (comulRingHom R B).comp (φ : A →ₐ[R] B).toRingHom =
      (Algebra.TensorProduct.map (φ : A →ₐ[R] B) (φ : A →ₐ[R] B)).toRingHom.comp
        (comulRingHom R A) := by
    refine RingHom.ext fun a => ?_
    exact (AlgHom.congr_fun (BialgHom.map_comp_comulAlgHom φ) a).symm
  have h₁ : (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B B).toRingHom.comp
      (φ : A →ₐ[R] B).toRingHom =
      (Algebra.TensorProduct.map (φ : A →ₐ[R] B) (φ : A →ₐ[R] B)).toRingHom.comp
        (Algebra.TensorProduct.includeLeft : A →ₐ[R] TensorProduct R A A).toRingHom := by
    refine RingHom.ext fun a => ?_
    simp
  have h₂ : (Algebra.TensorProduct.includeRight : B →ₐ[R] TensorProduct R B B).toRingHom.comp
      (φ : A →ₐ[R] B).toRingHom =
      (Algebra.TensorProduct.map (φ : A →ₐ[R] B) (φ : A →ₐ[R] B)).toRingHom.comp
        (Algebra.TensorProduct.includeRight : A →ₐ[R] TensorProduct R A A).toRingHom := by
    refine RingHom.ext fun a => ?_
    simp
  rw [map_map, map_map, map_map, hΔ, h₁, h₂, ← map_map, ← map_map, ← map_map, hx, map_add]

variable (p n) in

noncomputable def wittHomMap (φ : A →ₐc[R] B) : wittHom R p n A →+ wittHom R p n B where
  toFun x := ⟨map (φ : A →ₐ[R] B).toRingHom x, map_mem_wittHom φ x.2⟩
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

@[simp] theorem coe_wittHomMap (φ : A →ₐc[R] B) (x : wittHom R p n A) :
    (wittHomMap p n φ x : TruncatedWittVector p n B) = map (φ : A →ₐ[R] B).toRingHom x := rfl

theorem coeff_wittHomMap (φ : A →ₐc[R] B) (x : wittHom R p n A) (i : Fin n) :
    (wittHomMap p n φ x : TruncatedWittVector p n B).coeff i =
      φ ((x : TruncatedWittVector p n A).coeff i) :=
  coeff_map _ _ _

theorem wittHomMap_injective {φ : A →ₐc[R] B} (hφ : Injective φ) :
    Injective (wittHomMap p n φ) := fun _ _ h =>
  Subtype.ext (map_injective (f := (φ : A →ₐ[R] B).toRingHom) hφ (congrArg Subtype.val h))

end Map

theorem verschiebung_mem_wittHom {x : TruncatedWittVector p n A} (hx : x ∈ wittHom R p n A) :
    TruncWitt.verschiebung x ∈ wittHom R p n A := by
  rw [mem_wittHom_iff] at hx ⊢
  rw [map_verschiebung, map_verschiebung, map_verschiebung, hx, map_add]

variable (R p n A) in

noncomputable def wittHomVerschiebung : wittHom R p n A →+ wittHom R p n A where
  toFun x := ⟨TruncWitt.verschiebung x, verschiebung_mem_wittHom x.2⟩
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

@[simp] theorem coe_wittHomVerschiebung (x : wittHom R p n A) :
    (wittHomVerschiebung R p n A x : TruncatedWittVector p n A) = TruncWitt.verschiebung x := rfl

section CharP

variable [CharP R p]

variable (R p) in
omit hp in

theorem natCast_eq_zero_of_algebra (B : Type w) [CommRing B] [Algebra R B] : (p : B) = 0 := by
  rw [← map_natCast (algebraMap R B), CharP.cast_eq_zero, map_zero]

theorem frobeniusFun_mem_wittHom {x : TruncatedWittVector p n A} (hx : x ∈ wittHom R p n A) :
    TruncWitt.frobeniusFun x ∈ wittHom R p n A := by
  rw [mem_wittHom_iff] at hx ⊢
  rw [map_frobeniusFun, map_frobeniusFun, map_frobeniusFun, hx,
    frobeniusFun_add (natCast_eq_zero_of_algebra R p _)]

variable (R p n A) in

noncomputable def wittHomFrobenius : wittHom R p n A →+ wittHom R p n A where
  toFun x := ⟨TruncWitt.frobeniusFun x, frobeniusFun_mem_wittHom x.2⟩
  map_zero' := Subtype.ext frobeniusFun_zero
  map_add' _ _ := Subtype.ext (frobeniusFun_add (natCast_eq_zero_of_algebra R p A) _ _)

@[simp] theorem coe_wittHomFrobenius (x : wittHom R p n A) :
    (wittHomFrobenius R p n A x : TruncatedWittVector p n A) = TruncWitt.frobeniusFun x := rfl

theorem coeff_wittHomFrobenius (x : wittHom R p n A) (i : Fin n) :
    (wittHomFrobenius R p n A x : TruncatedWittVector p n A).coeff i =
      (x : TruncatedWittVector p n A).coeff i ^ p :=
  coeff_frobeniusFun _ _

theorem wittHomFrobenius_verschiebung (x : wittHom R p n A) :
    wittHomFrobenius R p n A (wittHomVerschiebung R p n A x) = (p : ℤ) • x :=
  Subtype.ext (frobeniusFun_verschiebung_eq_smul (natCast_eq_zero_of_algebra R p A) _)

theorem wittHomVerschiebung_frobenius (x : wittHom R p n A) :
    wittHomVerschiebung R p n A (wittHomFrobenius R p n A x) = (p : ℤ) • x :=
  Subtype.ext (verschiebung_frobeniusFun (natCast_eq_zero_of_algebra R p A) _)

variable (R p n A) in

noncomputable def wittHomDieudonneDatum : DieudonneDatum (p : ℤ) (wittHom R p n A) where
  F := (wittHomFrobenius R p n A).toIntLinearMap
  V := (wittHomVerschiebung R p n A).toIntLinearMap
  fv := LinearMap.ext fun x => wittHomFrobenius_verschiebung x
  vf := LinearMap.ext fun x => wittHomVerschiebung_frobenius x

@[simp] theorem wittHomDieudonneDatum_F_apply (x : wittHom R p n A) :
    (wittHomDieudonneDatum R p n A).F x = wittHomFrobenius R p n A x := rfl

@[simp] theorem wittHomDieudonneDatum_V_apply (x : wittHom R p n A) :
    (wittHomDieudonneDatum R p n A).V x = wittHomVerschiebung R p n A x := rfl

theorem wittHomMap_frobenius {B : Type w} [CommRing B] [Bialgebra R B] (φ : A →ₐc[R] B)
    (x : wittHom R p n A) :
    wittHomMap p n φ (wittHomFrobenius R p n A x) = wittHomFrobenius R p n B (wittHomMap p n φ x) :=
  Subtype.ext (map_frobeniusFun _ _)

end CharP

theorem wittHomMap_verschiebung {B : Type w} [CommRing B] [Bialgebra R B] (φ : A →ₐc[R] B)
    (x : wittHom R p n A) :
    wittHomMap p n φ (wittHomVerschiebung R p n A x) =
      wittHomVerschiebung R p n B (wittHomMap p n φ x) :=
  Subtype.ext (map_verschiebung _ _)

theorem shift_mem_wittHom {x : TruncatedWittVector p n A} (hx : x ∈ wittHom R p n A) :
    TruncWitt.shift x ∈ wittHom R p (n + 1) A := by
  rw [mem_wittHom_iff] at hx ⊢
  rw [map_shift, map_shift, map_shift, hx, map_add]

variable (R p n A) in

noncomputable def wittHomShift : wittHom R p n A →+ wittHom R p (n + 1) A where
  toFun x := ⟨TruncWitt.shift x, shift_mem_wittHom x.2⟩
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

@[simp] theorem coe_wittHomShift (x : wittHom R p n A) :
    (wittHomShift R p n A x : TruncatedWittVector p (n + 1) A) = TruncWitt.shift x := rfl

theorem wittHomShift_injective : Injective (wittHomShift R p n A) := fun _ _ h =>
  Subtype.ext (shift_injective (congrArg Subtype.val h))

theorem truncateLE_mem_wittHom {m : ℕ} (hm : n ≤ m) {x : TruncatedWittVector p m A}
    (hx : x ∈ wittHom R p m A) : TruncatedWittVector.truncate hm x ∈ wittHom R p n A := by
  rw [mem_wittHom_iff] at hx ⊢
  rw [map_truncateLE, map_truncateLE, map_truncateLE, hx, map_add]

variable (R p A) in

noncomputable def wittHomRestrict {m : ℕ} (hm : n ≤ m) : wittHom R p m A →+ wittHom R p n A where
  toFun x := ⟨TruncatedWittVector.truncate hm x, truncateLE_mem_wittHom hm x.2⟩
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

@[simp] theorem coe_wittHomRestrict {m : ℕ} (hm : n ≤ m) (x : wittHom R p m A) :
    (wittHomRestrict R p A hm x : TruncatedWittVector p n A) =
      TruncatedWittVector.truncate hm x := rfl

theorem wittHomRestrict_shift (x : wittHom R p n A) :
    wittHomRestrict R p A (Nat.le_succ n) (wittHomShift R p n A x) = wittHomVerschiebung R p n A x :=
  Subtype.ext (truncate_shift _)

theorem wittHomShift_restrict (y : wittHom R p (n + 1) A) :
    wittHomShift R p n A (wittHomRestrict R p A (Nat.le_succ n) y) =
      wittHomVerschiebung R p (n + 1) A y :=
  Subtype.ext (shift_truncate_succ _)

theorem wittHomShift_verschiebung (x : wittHom R p n A) :
    wittHomShift R p n A (wittHomVerschiebung R p n A x) =
      wittHomVerschiebung R p (n + 1) A (wittHomShift R p n A x) :=
  Subtype.ext (by
    rw [coe_wittHomShift, coe_wittHomVerschiebung, coe_wittHomVerschiebung, coe_wittHomShift,
      ← truncate_shift, shift_truncate_succ])

theorem wittHomShift_frobenius [CharP R p] (x : wittHom R p n A) :
    wittHomShift R p n A (wittHomFrobenius R p n A x) =
      wittHomFrobenius R p (n + 1) A (wittHomShift R p n A x) :=
  Subtype.ext (frobeniusFun_shift _).symm

theorem wittHomRestrict_verschiebung {m : ℕ} (hm : n ≤ m) (x : wittHom R p m A) :
    wittHomRestrict R p A hm (wittHomVerschiebung R p m A x) =
      wittHomVerschiebung R p n A (wittHomRestrict R p A hm x) :=
  Subtype.ext (verschiebung_truncateLE hm _).symm

theorem wittHomRestrict_frobenius [CharP R p] {m : ℕ} (hm : n ≤ m) (x : wittHom R p m A) :
    wittHomRestrict R p A hm (wittHomFrobenius R p m A x) =
      wittHomFrobenius R p n A (wittHomRestrict R p A hm x) :=
  Subtype.ext (frobeniusFun_truncateLE hm _).symm

theorem wittHomMap_shift {B : Type w} [CommRing B] [Bialgebra R B] (φ : A →ₐc[R] B)
    (x : wittHom R p n A) :
    wittHomMap p (n + 1) φ (wittHomShift R p n A x) = wittHomShift R p n B (wittHomMap p n φ x) :=
  Subtype.ext (map_shift _ _)

theorem wittHomMap_restrict {B : Type w} [CommRing B] [Bialgebra R B] (φ : A →ₐc[R] B)
    {m : ℕ} (hm : n ≤ m) (x : wittHom R p m A) :
    wittHomMap p n φ (wittHomRestrict R p A hm x) = wittHomRestrict R p B hm (wittHomMap p m φ x) :=
  Subtype.ext (map_truncateLE hm _ _)

end WittHom

end Deformation
