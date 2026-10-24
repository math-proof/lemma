import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private abbrev v2 {α : Type*} (a b : α) : Fin 2 → α := Matrix.vecCons a (Matrix.vecCons b Matrix.vecEmpty)

private abbrev m2 {α : Type*} (a b c d : α) : Matrix (Fin 2) (Fin 2) α := Matrix.of (Matrix.vecCons (v2 a b) (Matrix.vecCons (v2 c d) Matrix.vecEmpty))

private noncomputable def e (ℓ : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod ℓ) := m2 1 0 0 0

private noncomputable def f (ℓ : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod ℓ) := m2 0 0 0 1

private noncomputable def w (ℓ : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod ℓ) := m2 0 1 1 0

private lemma e_add_f {ℓ : ℕ} : e ℓ + f ℓ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e, f]

private lemma e_mul_e {ℓ : ℕ} : e ℓ * e ℓ = e ℓ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e, Matrix.mul_apply, Fin.sum_univ_two]

private lemma f_mul_f {ℓ : ℕ} : f ℓ * f ℓ = f ℓ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [f, Matrix.mul_apply, Fin.sum_univ_two]

private lemma e_mul_f {ℓ : ℕ} : e ℓ * f ℓ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e, f, Matrix.mul_apply, Fin.sum_univ_two]

private lemma f_mul_e {ℓ : ℕ} : f ℓ * e ℓ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e, f, Matrix.mul_apply, Fin.sum_univ_two]

private lemma w_mul_w {ℓ : ℕ} : w ℓ * w ℓ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w, Matrix.mul_apply, Fin.sum_univ_two]

private lemma w_mul_e {ℓ : ℕ} : w ℓ * e ℓ = f ℓ * w ℓ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w, e, f, Matrix.mul_apply, Fin.sum_univ_two]

private lemma e_mul_w {ℓ : ℕ} : e ℓ * w ℓ = w ℓ * f ℓ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w, e, f, Matrix.mul_apply, Fin.sum_univ_two]

private lemma decomp {ℓ : ℕ} (X : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) : X = X 0 0 • e ℓ + X 0 1 • (e ℓ * w ℓ) + X 1 0 • (w ℓ * e ℓ) + X 1 1 • f ℓ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w, e, f]

private lemma card_R {ℓ : ℕ} [Fact ℓ.Prime] : Nat.card (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) = ℓ ^ 4 := by
  let _ : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  rw [Nat.card_eq_fintype_card, show Fintype.card (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) = Fintype.card (Fin 2 → Fin 2 → ZMod ℓ) from rfl, Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  ring

private noncomputable def sc {ℓ : ℕ} (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] (c : ZMod ℓ) (v : V) : V := (algebraMap (ZMod ℓ) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) c) • v

private lemma smul_matrix_smul {ℓ : ℕ} (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] (c : ZMod ℓ) (X : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (v : V) : (c • X) • v = sc V c (X • v) := by
  rw [Algebra.smul_def, mul_smul]
  rfl

private lemma X_sc {ℓ : ℕ} (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] (X : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (c : ZMod ℓ) (v : V) : X • sc V c v = sc V c (X • v) := by
  show X • ((algebraMap (ZMod ℓ) _ c) • v) = (algebraMap (ZMod ℓ) _ c) • (X • v)
  rw [← mul_smul, ← mul_smul, Algebra.commutes]

private lemma sc_add {ℓ : ℕ} (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] (c : ZMod ℓ) (u v : V) : sc V c (u + v) = sc V c u + sc V c v := smul_add _ _ _

private lemma sc_zero {ℓ : ℕ} (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] (c : ZMod ℓ) : sc V c (0 : V) = 0 := smul_zero _

private lemma mul_sc {ℓ : ℕ} (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] (c d : ZMod ℓ) (v : V) : sc V (c * d) v = sc V c (sc V d v) := by
  show (algebraMap (ZMod ℓ) _ (c * d)) • v = _
  rw [map_mul, mul_smul]
  rfl

private lemma one_sc {ℓ : ℕ} (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] (v : V) : sc V (1 : ZMod ℓ) v = v := by
  show (algebraMap (ZMod ℓ) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) 1) • v = v
  rw [map_one, one_smul]

private lemma zero_sc {ℓ : ℕ} (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] (v : V) : sc V (0 : ZMod ℓ) v = 0 := by
  show (algebraMap (ZMod ℓ) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) 0) • v = 0
  rw [map_zero, zero_smul]

private lemma neg_sc {ℓ : ℕ} (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] (c : ZMod ℓ) (v : V) : sc V (-c) v = -(sc V c v) := by
  show (algebraMap (ZMod ℓ) _ (-c)) • v = _
  rw [map_neg, neg_smul]
  rfl

private lemma e_add_f_smul {ℓ : ℕ} (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] (v : V) : e ℓ • v + f ℓ • v = v := by
  rw [← add_smul, e_add_f, one_smul]

private lemma e_e {ℓ : ℕ} (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] (v : V) : e ℓ • (e ℓ • v) = e ℓ • v := by
  rw [← mul_smul, e_mul_e]

private lemma e_f {ℓ : ℕ} (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] (v : V) : e ℓ • (f ℓ • v) = 0 := by
  rw [← mul_smul, e_mul_f, zero_smul]

private lemma f_e {ℓ : ℕ} (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] (v : V) : f ℓ • (e ℓ • v) = 0 := by
  rw [← mul_smul, f_mul_e, zero_smul]

private lemma w_w {ℓ : ℕ} (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] (v : V) : w ℓ • (w ℓ • v) = v := by
  rw [← mul_smul, w_mul_w, one_smul]

private lemma w_e {ℓ : ℕ} (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] (v : V) : w ℓ • (e ℓ • v) = f ℓ • (w ℓ • v) := by
  rw [← mul_smul, w_mul_e, mul_smul]

private lemma e_w {ℓ : ℕ} (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] (v : V) : e ℓ • (w ℓ • v) = w ℓ • (f ℓ • v) := by
  rw [← mul_smul, e_mul_w, mul_smul]

private lemma e_w_of_e {ℓ : ℕ} (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] {v : V} (hv : e ℓ • v = v) : e ℓ • (w ℓ • v) = 0 := by
  rw [e_w, ← hv, f_e, smul_zero]

private lemma f_of_e {ℓ : ℕ} (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] {v : V} (hv : e ℓ • v = v) : f ℓ • v = 0 := by
  rw [← hv, f_e]

private lemma f_w_of_e {ℓ : ℕ} (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] {v : V} (hv : e ℓ • v = v) : f ℓ • (w ℓ • v) = w ℓ • v := by
  rw [← w_e, hv]

private noncomputable def split {ℓ : ℕ} (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] : V ≃ Subtype (fun (v : V) => e ℓ • v = v) × Subtype (fun (v : V) => e ℓ • v = v) where
  toFun v := (⟨e ℓ • v, e_e V v⟩, ⟨e ℓ • (w ℓ • v), e_e V _⟩)
  invFun p := (p.1 : V) + w ℓ • (p.2 : V)
  left_inv v := by
    show e ℓ • v + w ℓ • (e ℓ • (w ℓ • v)) = v
    rw [e_w, w_w, e_add_f_smul]
  right_inv p := by
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := p
    simp only [Prod.mk.injEq, Subtype.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [smul_add, hx, e_w_of_e V hy, add_zero]
    · rw [smul_add, smul_add, e_w_of_e V hx, zero_add, w_w, hy]

private lemma natCard_eFixed {ℓ : ℕ} (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] [Fact ℓ.Prime] [Finite V] (hV : Nat.card V = ℓ ^ 4) : Nat.card (Subtype fun (v : V) => e ℓ • v = v) = ℓ ^ 2 := by
  have h := Nat.card_congr (split V (ℓ := ℓ))
  rw [Nat.card_prod, hV] at h
  have : (Nat.card (Subtype fun (v : V) => e ℓ • v = v)) ^ 2 = (ℓ ^ 2) ^ 2 := by
    rw [sq, ← h]
    ring
  exact Nat.pow_left_injective two_ne_zero this

private lemma exists_indep {ℓ : ℕ} (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] [Fact ℓ.Prime] [Finite V] (hV : Nat.card V = ℓ ^ 4) : ∃ v₁ v₂ : V, e ℓ • v₁ = v₁ ∧ e ℓ • v₂ = v₂ ∧ ∀ α β : ZMod ℓ, sc V α v₁ + sc V β v₂ = 0 → α = 0 ∧ β = 0 := by
  classical
  have hcard := natCard_eFixed V hV
  have hℓ : 1 < ℓ := (Fact.out : ℓ.Prime).one_lt
  have h1 : 1 < Nat.card (Subtype fun (v : V) => e ℓ • v = v) := by
    rw [hcard]
    exact Nat.one_lt_pow two_ne_zero hℓ
  let _ : Nontrivial (Subtype fun (v : V) => e ℓ • v = v) := Finite.one_lt_card_iff_nontrivial.mp h1
  obtain ⟨⟨v₁, hv₁⟩, hne⟩ := exists_ne (⟨0, smul_zero _⟩ : Subtype fun (v : V) => e ℓ • v = v)
  have hv₁0 : v₁ ≠ 0 := fun h => hne (Subtype.ext h)
  let line : ZMod ℓ → Subtype (fun (v : V) => e ℓ • v = v) := fun c => ⟨sc V c v₁, by rw [X_sc, hv₁]⟩
  have hlt : Nat.card (Set.range line) < Nat.card (Subtype fun (v : V) => e ℓ • v = v) := calc
    _ ≤ Nat.card (ZMod ℓ) := Finite.card_range_le line
    _ = ℓ := by
      rw [Nat.card_eq_fintype_card, ZMod.card]
    _ < ℓ ^ 2 := by
      nlinarith
    _ = Nat.card (Subtype fun (v : V) => e ℓ • v = v) := hcard.symm
  have hnot : ∃ v₂ : Subtype fun (v : V) => e ℓ • v = v, v₂ ∉ Set.range line := by
    by_contra h
    push Not at h
    have : Set.range line = Set.univ := Set.eq_univ_of_forall h
    rw [this, Nat.card_univ] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨⟨v₂, hv₂⟩, hv₂n⟩ := hnot
  refine ⟨v₁, v₂, hv₁, hv₂, fun α β hαβ => ?_⟩
  if hβ : β = 0 then
    refine ⟨?_, hβ⟩
    rw [hβ, zero_sc, add_zero] at hαβ
    by_contra hα
    apply hv₁0
    have := congrArg (sc V α⁻¹) hαβ
    rwa [← mul_sc, inv_mul_cancel₀ hα, one_sc, sc_zero] at this
  else
    exfalso
    apply hv₂n
    have h2 : sc V β v₂ = -(sc V α v₁) := eq_neg_of_add_eq_zero_right hαβ
    have h3 : v₂ = sc V (-(β⁻¹ * α)) v₁ := by
      have := congrArg (sc V β⁻¹) h2
      rw [← mul_sc, inv_mul_cancel₀ hβ, one_sc] at this
      rw [this, ← neg_sc, ← mul_sc, neg_mul_eq_mul_neg]
    refine ⟨-(β⁻¹ * α), Subtype.ext h3.symm⟩

private lemma eq_zero_of_smul_gen_eq_zero {ℓ : ℕ} (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] [Fact ℓ.Prime] {v₁ v₂ : V} (hv₁ : e ℓ • v₁ = v₁) (hv₂ : e ℓ • v₂ = v₂) (hind : ∀ α β : ZMod ℓ, sc V α v₁ + sc V β v₂ = 0 → α = 0 ∧ β = 0) (X : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (hX : X • (v₁ + w ℓ • v₂) = 0) : X = 0 := by
  have a2 : (e ℓ * w ℓ) • v₁ = 0 := by rw [mul_smul, e_w_of_e V hv₁]
  have a3 : (w ℓ * e ℓ) • v₁ = w ℓ • v₁ := by rw [mul_smul, hv₁]
  have a4 : f ℓ • v₁ = 0 := f_of_e V hv₁
  have b1 : e ℓ • (w ℓ • v₂) = 0 := e_w_of_e V hv₂
  have b2 : (e ℓ * w ℓ) • (w ℓ • v₂) = v₂ := by rw [mul_smul, w_w, hv₂]
  have b3 : (w ℓ * e ℓ) • (w ℓ • v₂) = 0 := by rw [mul_smul, e_w_of_e V hv₂, smul_zero]
  have b4 : f ℓ • (w ℓ • v₂) = w ℓ • v₂ := f_w_of_e V hv₂
  have h0 := hX
  rw [decomp X] at h0
  simp only [add_smul, smul_add, smul_matrix_smul, hv₁, a2, a3, a4, b1, b2, b3, b4, sc_zero, add_zero, zero_add] at h0
  have he := congrArg (fun t => e ℓ • t) h0
  simp only [smul_add, smul_zero, X_sc, hv₁, hv₂, e_w_of_e V hv₁, e_w_of_e V hv₂, sc_zero, add_zero] at he
  obtain ⟨ha, hb⟩ := hind _ _ he
  have hf := congrArg (fun t => w ℓ • (f ℓ • t)) h0
  simp only [smul_add, smul_zero, X_sc, a4, f_of_e V hv₂, b4, f_w_of_e V hv₁, w_w, sc_zero, zero_add] at hf
  obtain ⟨hc, hd⟩ := hind _ _ hf
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]

private lemma nonempty_linearEquiv (ℓ : ℕ) [Fact ℓ.Prime] (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] [Finite V] (hV : Nat.card V = ℓ ^ 4) : Nonempty (V ≃ₗ[Matrix (Fin 2) (Fin 2) (ZMod ℓ)] Matrix (Fin 2) (Fin 2) (ZMod ℓ)) := by
  classical
  obtain ⟨v₁, v₂, hv₁, hv₂, hind⟩ := exists_indep V hV
  let T : Matrix (Fin 2) (Fin 2) (ZMod ℓ) →ₗ[Matrix (Fin 2) (Fin 2) (ZMod ℓ)] V :=
    { toFun := fun X => X • (v₁ + w ℓ • v₂)
      map_add' := fun X Y => add_smul X Y _
      map_smul' := fun a X => mul_smul a X _ }
  have hT : ∀ X, T X = X • (v₁ + w ℓ • v₂) := fun X => rfl
  have hTinj : Function.Injective T := by
    intro X Y hXY
    rw [hT, hT] at hXY
    have h0 : (X - Y) • (v₁ + w ℓ • v₂) = 0 := by rw [sub_smul, hXY, sub_self]
    refine sub_eq_zero.mp (eq_zero_of_smul_gen_eq_zero V hv₁ hv₂ hind (X - Y) h0)
  have hTbij : Function.Bijective T := hTinj.bijective_of_nat_card_le (by rw [hV, card_R])
  refine ⟨(LinearEquiv.ofBijective T hTbij).symm⟩

private lemma exists_natCard_eq_pow (ℓ : ℕ) [Fact ℓ.Prime] (W : Type) [AddCommGroup W] [Finite W] (hW : ∀ w : W, ℓ • w = 0) : ∃ n : ℕ, Nat.card W = ℓ ^ n := by
  have hp : IsPGroup ℓ (Multiplicative W) := by
    intro g
    refine ⟨1, ?_⟩
    rw [pow_one]
    change Multiplicative.ofAdd ((ℓ : ℕ) • Multiplicative.toAdd g) = Multiplicative.ofAdd 0
    rw [hW]
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  refine ⟨n, ?_⟩
  rw [← hn]
  exact Nat.card_congr Multiplicative.ofAdd

private noncomputable def eFixed {ℓ : ℕ} (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] : AddSubgroup V where
  carrier := {v | e ℓ • v = v}
  zero_mem' := smul_zero _
  add_mem' := by
    intro u v hu hv
    show e ℓ • (u + v) = u + v
    rw [smul_add, hu, hv]
  neg_mem' := by
    intro v hv
    show e ℓ • (-v) = -v
    rw [smul_neg, hv]

private lemma nsmul_eq_zero {ℓ : ℕ} (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] [Fact ℓ.Prime] (v : V) : ℓ • v = 0 := by
  have h : ((ℓ : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [← Nat.cast_smul_eq_nsmul (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) ℓ v, h, zero_smul]

private lemma helper_main {ℓ : ℕ} (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] [Fact ℓ.Prime] [Finite V] : ∃ k : ℕ, Nat.card V = ℓ ^ (2 * k) := by
  classical
  have hsplit : Nat.card V = Nat.card (eFixed V (ℓ := ℓ)) * Nat.card (eFixed V (ℓ := ℓ)) := by
    rw [Nat.card_congr (split V (ℓ := ℓ)), Nat.card_prod]
    rfl
  let _ : Finite (eFixed V (ℓ := ℓ)) := inferInstance
  obtain ⟨j, hj⟩ := exists_natCard_eq_pow ℓ (eFixed V (ℓ := ℓ)) (fun w => by
    apply Subtype.ext
    show ((ℓ • w : eFixed V (ℓ := ℓ)) : V) = 0
    rw [AddSubgroup.coe_nsmul]
    exact nsmul_eq_zero V (w : V))
  refine ⟨j, ?_⟩
  rw [hsplit, hj, ← pow_add, two_mul]

/--
[Matrix_exists_natCard_eq_pow_two_mul_of_module_zmod](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Matrix_exists_natCard_eq_pow_two_mul_of_module_zmod.lean)
-/
@[path]
private lemma main
  (ℓ : ℕ) [Fact ℓ.Prime]
  (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] [Finite V] :
  -- imply
  ∃ k : ℕ, Nat.card V = ℓ ^ (2 * k) :=
  helper_main (ℓ := ℓ) V


-- created on 2026-10-20
