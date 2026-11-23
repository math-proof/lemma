module

public import Mathlib
public import Theorem.AlgHom.Basic
public import Theorem.WeierstrassCurve.TateModule
public import Instance.PDivisibleGroup_Points

public noncomputable section

set_option autoImplicit false

noncomputable section

open scoped TensorProduct
open Coalgebra Bialgebra WithConv

namespace PDivisibleGroup.Hopf

section AntipodeAlgHom

open HopfAlgebra

variable (R : Type*) [CommSemiring R] (H : Type*) [CommSemiring H] [HopfAlgebra R H]


@[simp] public theorem antipodeAlgHom_apply (x : H) : antipodeAlgHom R H x = antipode R x := rfl


public theorem antipodeAlgHom_toLinearMap : (antipodeAlgHom R H).toLinearMap = antipode R := rfl

variable {R H}
variable {A : Type*} [CommSemiring A] [Algebra R A]


public theorem lift_comp_antipodeAlgHom_apply (φ : H →ₐ[R] A) (z : H ⊗[R] H) :
    Algebra.TensorProduct.lift φ (φ.comp (antipodeAlgHom R H)) (fun _ _ => .all _ _) z =
      φ (LinearMap.mul' R H ((antipode R).lTensor H z)) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.lTensor_tmul]
  | add x y hx hy => simp [map_add, hx, hy]


public theorem lift_antipodeAlgHom_comp_apply (φ : H →ₐ[R] A) (z : H ⊗[R] H) :
    Algebra.TensorProduct.lift (φ.comp (antipodeAlgHom R H)) φ (fun _ _ => .all _ _) z =
      φ (LinearMap.mul' R H ((antipode R).rTensor H z)) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.rTensor_tmul]
  | add x y hx hy => simp [map_add, hx, hy]


public theorem convMul_comp_antipodeAlgHom (φ : H →ₐ[R] A) :
    toConv φ * toConv (φ.comp (antipodeAlgHom R H)) = 1 := by
  refine WithConv.ext (AlgHom.ext fun x => ?_)
  change (toConv φ * toConv (φ.comp (antipodeAlgHom R H))) x = (1 : WithConv (H →ₐ[R] A)) x
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply, ofConv_toConv, ofConv_toConv,
    lift_comp_antipodeAlgHom_apply, mul_antipode_lTensor_comul_apply, AlgHom.commutes]


public theorem comp_antipodeAlgHom_convMul (φ : H →ₐ[R] A) :
    toConv (φ.comp (antipodeAlgHom R H)) * toConv φ = 1 := by
  refine WithConv.ext (AlgHom.ext fun x => ?_)
  change (toConv (φ.comp (antipodeAlgHom R H)) * toConv φ) x = (1 : WithConv (H →ₐ[R] A)) x
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply, ofConv_toConv, ofConv_toConv,
    lift_antipodeAlgHom_comp_apply, mul_antipode_rTensor_comul_apply, AlgHom.commutes]


public theorem isUnit_toConv_algHom (φ : H →ₐ[R] A) : IsUnit (toConv φ) :=
  isUnit_iff_exists.2 ⟨_, convMul_comp_antipodeAlgHom φ, comp_antipodeAlgHom_convMul φ⟩

end AntipodeAlgHom

section ConvComp

variable {R : Type*} [CommSemiring R] {H K : Type*} [CommSemiring H] [CommSemiring K]
  [Bialgebra R H] [Bialgebra R K]
variable (A : Type*) [CommSemiring A] [Algebra R A]


@[simp] public theorem convCompMonoidHom_apply (π : H →ₐc[R] K) (f : WithConv (K →ₐ[R] A)) :
    convCompMonoidHom A π f = toConv (f.ofConv.comp (π : H →ₐ[R] K)) := rfl

end ConvComp

end PDivisibleGroup.Hopf

namespace PDivisibleGroup

variable {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
variable (L : Type) [CommRing L] [Algebra R L]


@[simp] public theorem toAlgHom_ofAlgHom (f : G.level v →ₐ[R] L) : toAlgHom (ofAlgHom f : G.Point L v) = f := rfl

@[simp] public theorem ofAlgHom_toAlgHom (x : G.Point L v) : ofAlgHom (toAlgHom x) = x := rfl

@[simp] public theorem toConv_ofConv (f : WithConv (G.level v →ₐ[R] L)) : toConv (ofConv f : G.Point L v) = f := rfl

@[simp] public theorem ofConv_toConv (x : G.Point L v) : ofConv (toConv x) = x := rfl

public theorem toConv_eq (x : G.Point L v) : toConv x = WithConv.toConv (toAlgHom x) := rfl


@[ext] public theorem ext {x y : G.Point L v} (hxy : ∀ a, toAlgHom x a = toAlgHom y a) : x = y :=
  WithConv.ext (AlgHom.ext hxy)


public theorem toConv_mul (x y : G.Point L v) : toConv (x * y) = toConv x * toConv y := rfl

public theorem toConv_one : toConv (1 : G.Point L v) = 1 := rfl

public theorem toConv_pow (x : G.Point L v) (n : ℕ) : toConv (x ^ n) = toConv x ^ n := rfl

public theorem ofConv_mul (f g : WithConv (G.level v →ₐ[R] L)) : (ofConv (f * g) : G.Point L v) = ofConv f * ofConv g := rfl

public theorem ofConv_pow (f : WithConv (G.level v →ₐ[R] L)) (n : ℕ) : (ofConv (f ^ n) : G.Point L v) = ofConv f ^ n := rfl


public theorem one_apply (a : G.level v) : toAlgHom (1 : G.Point L v) a = algebraMap R L (counit (R := R) a) := rfl


public theorem mul_apply (x y : G.Point L v) (a : G.level v) :
    toAlgHom (x * y) a =
      Algebra.TensorProduct.lift (toAlgHom x) (toAlgHom y) (fun _ _ => .all _ _) (comul (R := R) a) :=
  AlgHom.convMul_apply _ _ a


public theorem isUnit (x : G.Point L v) : IsUnit x :=
  Hopf.isUnit_toConv_algHom (toAlgHom x)


public theorem inv_eq (x : G.Point L v) :
    x⁻¹ = ofAlgHom ((toAlgHom x).comp (Hopf.antipodeAlgHom R (G.level v))) := by
  apply mul_left_cancel (a := x)
  rw [mul_inv_cancel]
  exact (Hopf.convMul_comp_antipodeAlgHom (toAlgHom x)).symm


public theorem pow_card_eq_one (x : G.Point L v) : x ^ (p ^ v) = 1 :=
  G.point_pow_eq_one v (toConv x)


public theorem toAlgHom_pow (x : G.Point L v) (n : ℕ) :
    toAlgHom (x ^ n) = (toAlgHom x).comp (Hopf.nsmulAlgHom R (G.level v) n) :=
  congrArg WithConv.ofConv (Hopf.toConv_pow_eq_toConv_comp_nsmulAlgHom (toAlgHom x) n)

end Point


public theorem toAlgHom_pointIncl (v : ℕ) (x : G.Point L v) :
    Point.toAlgHom (G.pointIncl L v x) = (Point.toAlgHom x).comp (G.transitionAlgHom v) := rfl


@[simp] public theorem pointIncl_apply (v : ℕ) (x : G.Point L v) (a : G.level (v + 1)) :
    Point.toAlgHom (G.pointIncl L v x) a = Point.toAlgHom x (G.transition v a) := rfl


public theorem pointIncl_injective (v : ℕ) : Function.Injective (G.pointIncl L v) := by
  intro x y hxy
  have h := G.comp_transition_injective v (L := L)
    (show (Point.toAlgHom x).comp (G.transitionAlgHom v) = (Point.toAlgHom y).comp (G.transitionAlgHom v)
      from congrArg Point.toAlgHom hxy)
  exact Point.ext fun a => DFunLike.congr_fun h a


public theorem mem_range_pointIncl_iff (v : ℕ) (y : G.Point L (v + 1)) :
    y ∈ Set.range (G.pointIncl L v) ↔ y ^ (p ^ v) = 1 := by
  change _ ↔ Point.toConv y ^ (p ^ v) = 1
  rw [← (G.exists_comp_transition_eq_iff v (Point.toConv y))]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Point.toAlgHom x, rfl⟩
  · rintro ⟨g, hg⟩
    exact ⟨Point.ofAlgHom g, Point.ext fun a => DFunLike.congr_fun hg a⟩


public theorem exists_pointIncl_eq_of_pow_eq_one (v : ℕ) (y : G.Point L (v + 1)) (hy : y ^ (p ^ v) = 1) :
    ∃ x : G.Point L v, G.pointIncl L v x = y :=
  (G.mem_range_pointIncl_iff v y).2 hy

variable (L)


@[simp] public theorem pointInclLE_self (v : ℕ) (x : G.Point L v) : G.pointInclLE L (le_refl v) x = x := by
  rw [pointInclLE, Nat.leRec_self]
  rfl


public theorem pointInclLE_succ {v w : ℕ} (hvw : v ≤ w) (x : G.Point L v) :
    G.pointInclLE L (Nat.le_succ_of_le hvw) x = G.pointIncl L w (G.pointInclLE L hvw x) := by
  rw [pointInclLE, Nat.leRec_succ (h1 := hvw)]
  rfl


public theorem pointInclLE_succ_self (v : ℕ) (x : G.Point L v) :
    G.pointInclLE L (Nat.le_succ v) x = G.pointIncl L v x := by
  rw [G.pointInclLE_succ (le_refl v), G.pointInclLE_self]


public theorem pointInclLE_trans {u v w : ℕ} (huv : u ≤ v) (hvw : v ≤ w) (x : G.Point L u) :
    G.pointInclLE L (huv.trans hvw) x = G.pointInclLE L hvw (G.pointInclLE L huv x) := by
  induction hvw with
  | refl => rw [G.pointInclLE_self]
  | step hvw ih =>
    rw [G.pointInclLE_succ hvw, ← ih]
    exact G.pointInclLE_succ (huv.trans hvw) x


public theorem pointInclLE_injective {v w : ℕ} (hvw : v ≤ w) : Function.Injective (G.pointInclLE L hvw) := by
  induction hvw with
  | refl => intro x y hxy; rwa [G.pointInclLE_self, G.pointInclLE_self] at hxy
  | step hvw ih =>
    intro x y hxy
    rw [G.pointInclLE_succ hvw, G.pointInclLE_succ hvw] at hxy
    exact ih (G.pointIncl_injective _ hxy)


public theorem exists_pointInclLE_eq_of_pow_eq_one {v w : ℕ} (hvw : v ≤ w) (y : G.Point L w)
    (hy : y ^ (p ^ v) = 1) : ∃ x : G.Point L v, G.pointInclLE L hvw x = y := by
  induction hvw with
  | refl => exact ⟨y, G.pointInclLE_self v y⟩
  | @step w hvw ih =>

    have hyw : y ^ (p ^ w) = 1 := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hvw
      have hpw : p ^ w = p ^ v * p ^ k := by rw [hk, pow_add]
      rw [hpw, pow_mul, hy, one_pow]
    obtain ⟨z, rfl⟩ := G.exists_pointIncl_eq_of_pow_eq_one w y hyw
    have hz : z ^ (p ^ v) = 1 := G.pointIncl_injective w (by rw [map_pow, hy, map_one])
    obtain ⟨x, rfl⟩ := ih z hz
    exact ⟨x, G.pointInclLE_succ hvw x⟩


public theorem pointsMk_apply (v : ℕ) (x : G.Point L v) :
    G.pointsMk L v x = Multiplicative.ofAdd (G.pointsMkAdd L v (Additive.ofMul x)) := rfl


public theorem toAdd_pointsMk (v : ℕ) (x : G.Point L v) :
    (G.pointsMk L v x).toAdd = G.pointsMkAdd L v (Additive.ofMul x) := rfl


@[simp] public theorem pointsMkAdd_pointInclLE {v w : ℕ} (hvw : v ≤ w) (x : G.Point L v) :
    G.pointsMkAdd L w (Additive.ofMul (G.pointInclLE L hvw x)) = G.pointsMkAdd L v (Additive.ofMul x) :=
  AddCommGroup.DirectLimit.of_f (G := fun v => Additive (G.Point L v)) hvw (Additive.ofMul x)


@[simp] public theorem pointsMkAdd_pointIncl (v : ℕ) (x : G.Point L v) :
    G.pointsMkAdd L (v + 1) (Additive.ofMul (G.pointIncl L v x)) = G.pointsMkAdd L v (Additive.ofMul x) := by
  rw [← G.pointInclLE_succ_self, pointsMkAdd_pointInclLE]


@[simp] public theorem pointsMk_pointInclLE {v w : ℕ} (hvw : v ≤ w) (x : G.Point L v) :
    G.pointsMk L w (G.pointInclLE L hvw x) = G.pointsMk L v x :=
  congrArg Multiplicative.ofAdd (G.pointsMkAdd_pointInclLE hvw x)


@[simp] public theorem pointsMk_pointIncl (v : ℕ) (x : G.Point L v) :
    G.pointsMk L (v + 1) (G.pointIncl L v x) = G.pointsMk L v x :=
  congrArg Multiplicative.ofAdd (G.pointsMkAdd_pointIncl v x)


public theorem Points.exists_mkAdd (z : G.Points L) : ∃ (v : ℕ) (x : G.Point L v), G.pointsMkAdd L v (Additive.ofMul x) = z := by
  refine AddCommGroup.DirectLimit.induction_on (G := fun v => Additive (G.Point L v))
    (f := fun v w hvw => G.pointsDirectedSystemMap v w hvw)
    (C := fun z : G.Points L => ∃ (v : ℕ) (x : G.Point L v), G.pointsMkAdd L v (Additive.ofMul x) = z) z ?_
  intro v x
  exact ⟨v, Additive.toMul x, rfl⟩


public theorem Points.induction_on {C : G.Points L → Prop} (z : G.Points L)
    (ih : ∀ (v : ℕ) (x : G.Point L v), C (G.pointsMkAdd L v (Additive.ofMul x))) : C z := by
  obtain ⟨v, x, rfl⟩ := Points.exists_mkAdd G z
  exact ih v x


public theorem pointsMkAdd_injective (v : ℕ) : Function.Injective (G.pointsMkAdd L v) := by
  intro x y hxy
  have h0 : G.pointsMkAdd L v (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  obtain ⟨w, hvw, hw⟩ := AddCommGroup.DirectLimit.of.zero_exact (G := fun v => Additive (G.Point L v))
    (f := fun v w hvw => G.pointsDirectedSystemMap v w hvw) v (x - y) h0
  have hinj := G.pointInclLE_injective (L := L) hvw
  have hw' : G.pointInclLE L hvw (Additive.toMul (x - y)) = 1 := hw
  have : Additive.toMul (x - y) = 1 := hinj (by rw [hw', map_one])
  exact sub_eq_zero.1 this


public theorem pointsMk_injective (v : ℕ) : Function.Injective (G.pointsMk L v) := fun _ _ hxy =>
  G.pointsMkAdd_injective v (congrArg Multiplicative.toAdd hxy)


public theorem pointsMkAdd_eq_pointsMkAdd_iff {v : ℕ} (x y : G.Point L v) :
    G.pointsMkAdd L v (Additive.ofMul x) = G.pointsMkAdd L v (Additive.ofMul y) ↔ x = y :=
  ⟨fun hxy => G.pointsMkAdd_injective v hxy, fun hxy => by rw [hxy]⟩


public theorem nsmul_pointsMkAdd_eq_zero (v : ℕ) (x : G.Point L v) :
    (p ^ v) • G.pointsMkAdd L v (Additive.ofMul x) = 0 := by
  rw [← map_nsmul, ← ofMul_pow, Point.pow_card_eq_one, ofMul_one, map_zero]


public theorem isTorsion_points_of_pos (hp : 0 < p) (z : G.Points L) : ∃ n : ℕ, 0 < n ∧ n • z = 0 := by
  obtain ⟨v, x, rfl⟩ := Points.exists_mkAdd G z
  exact ⟨p ^ v, pow_pos hp v, G.nsmul_pointsMkAdd_eq_zero v x⟩

section Map

variable {L' : Type} [CommRing L'] [Algebra R L'] {L'' : Type} [CommRing L''] [Algebra R L'']


@[simp] public theorem toAlgHom_pointMap (φ : L →ₐ[R] L') (v : ℕ) (x : G.Point L v) :
    Point.toAlgHom (G.pointMap φ v x) = φ.comp (Point.toAlgHom x) := rfl


public theorem pointMap_id (v : ℕ) : G.pointMap (AlgHom.id R L) v = MonoidHom.id _ :=
  MonoidHom.ext fun _ => Point.ext fun _ => rfl


public theorem pointMap_comp (φ : L →ₐ[R] L') (ψ : L' →ₐ[R] L'') (v : ℕ) :
    G.pointMap (ψ.comp φ) v = (G.pointMap ψ v).comp (G.pointMap φ v) :=
  MonoidHom.ext fun _ => Point.ext fun _ => rfl


public theorem pointMap_pointIncl (φ : L →ₐ[R] L') (v : ℕ) (x : G.Point L v) :
    G.pointMap φ (v + 1) (G.pointIncl L v x) = G.pointIncl L' v (G.pointMap φ v x) :=
  Point.ext fun _ => rfl


public theorem pointMap_pointInclLE (φ : L →ₐ[R] L') {v w : ℕ} (hvw : v ≤ w) (x : G.Point L v) :
    G.pointMap φ w (G.pointInclLE L hvw x) = G.pointInclLE L' hvw (G.pointMap φ v x) := by
  induction hvw with
  | refl => rw [G.pointInclLE_self, G.pointInclLE_self]
  | step hvw ih => rw [G.pointInclLE_succ hvw, G.pointInclLE_succ hvw, pointMap_pointIncl, ih]


@[simp] public theorem pointsMap_pointsMkAdd (φ : L →ₐ[R] L') (v : ℕ) (x : G.Point L v) :
    G.pointsMap φ (G.pointsMkAdd L v (Additive.ofMul x)) = G.pointsMkAdd L' v (Additive.ofMul (G.pointMap φ v x)) :=
  AddCommGroup.DirectLimit.map_apply_of (G := fun v => Additive (G.Point L v)) (G' := fun v => Additive (G.Point L' v))
    (f := fun v w hvw => G.pointsDirectedSystemMap v w hvw)
    (f' := fun v w hvw => G.pointsDirectedSystemMap v w hvw)
    (fun v => MonoidHom.toAdditive (G.pointMap φ v)) _ (Additive.ofMul x)


public theorem pointsMap_id : G.pointsMap (AlgHom.id R L) = AddMonoidHom.id _ := by
  refine AddCommGroup.DirectLimit.hom_ext (G := fun v => Additive (G.Point L v))
    (f := fun v w hvw => G.pointsDirectedSystemMap v w hvw) (P := G.Points L) fun v => ?_
  refine AddMonoidHom.ext fun x => ?_
  change G.pointsMap (AlgHom.id R L) (G.pointsMkAdd L v x) = G.pointsMkAdd L v x
  exact G.pointsMap_pointsMkAdd (AlgHom.id R L) v (Additive.toMul x)


public theorem pointsMap_comp (φ : L →ₐ[R] L') (ψ : L' →ₐ[R] L'') :
    G.pointsMap (ψ.comp φ) = (G.pointsMap ψ).comp (G.pointsMap φ) := by
  refine AddCommGroup.DirectLimit.hom_ext (G := fun v => Additive (G.Point L v))
    (f := fun v w hvw => G.pointsDirectedSystemMap v w hvw) (P := G.Points L'') fun v => ?_
  refine AddMonoidHom.ext fun x => ?_
  change G.pointsMap (ψ.comp φ) (G.pointsMkAdd L v x) = G.pointsMap ψ (G.pointsMap φ (G.pointsMkAdd L v x))
  rw [show x = Additive.ofMul (Additive.toMul x) from rfl, pointsMap_pointsMkAdd, pointsMap_pointsMkAdd,
    pointsMap_pointsMkAdd, pointMap_comp]
  rfl


public theorem pointsMap_injective_of_injective (φ : L →ₐ[R] L') (hφ : Function.Injective φ) :
    Function.Injective (G.pointsMap φ) := by
  intro z w hzw
  induction z using Points.induction_on with
  | ih v x =>
    induction w using Points.induction_on with
    | ih w y =>

      rw [← G.pointsMkAdd_pointInclLE (le_max_left v w) x, ← G.pointsMkAdd_pointInclLE (le_max_right v w) y]
        at hzw ⊢
      rw [pointsMap_pointsMkAdd, pointsMap_pointsMkAdd, pointsMkAdd_eq_pointsMkAdd_iff] at hzw
      rw [pointsMkAdd_eq_pointsMkAdd_iff]
      refine Point.ext fun a => hφ ?_
      exact DFunLike.congr_fun (congrArg Point.toAlgHom hzw) a

end Map


public theorem Points.smul_def (σ : L ≃ₐ[R] L) (z : G.Points L) : σ • z = G.pointsMap (σ : L →ₐ[R] L) z := rfl


@[simp] public theorem Points.smul_pointsMkAdd (σ : L ≃ₐ[R] L) (v : ℕ) (x : G.Point L v) :
    σ • G.pointsMkAdd L v (Additive.ofMul x) =
      G.pointsMkAdd L v (Additive.ofMul (G.pointMap (σ : L →ₐ[R] L) v x)) :=
  G.pointsMap_pointsMkAdd _ v x

section Tate

variable [Fact p.Prime]
variable (L)


public theorem tateModuleRep_apply (σ : L ≃ₐ[R] L) (x : TateModule p (G.Points L)) (n : ℕ) :
    ((G.tateModuleRep L σ x : TateModule p (G.Points L)) : ℕ → G.Points L) n = σ • (x : ℕ → G.Points L) n :=
  rfl

end Tate

end PDivisibleGroup

end
