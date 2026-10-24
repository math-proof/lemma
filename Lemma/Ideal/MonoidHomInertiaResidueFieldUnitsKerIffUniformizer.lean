import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

section

variable {B : Type u} [CommRing B] {G : Type v} [Group G] [MulSemiringAction G B]
private lemma smul_mem_of_mem_inertia (𝔓 : Ideal B) {σ : G} (hσ : σ ∈ 𝔓.inertia G) {z : B} (hz : z ∈ 𝔓) : σ • z ∈ 𝔓 := by
  have h : σ • z - z ∈ 𝔓 := hσ z
  have : σ • z = (σ • z - z) + z := by ring
  rw [this]; apply 𝔓.add_mem h hz
private lemma smul_mem_sq_of_mem_inertia (𝔓 : Ideal B) {σ : G} (hσ : σ ∈ 𝔓.inertia G) {z : B} (hz : z ∈ 𝔓 ^ 2) : σ • z ∈ 𝔓 ^ 2 := by
  let f : B →+* B := MulSemiringAction.toRingHom G B σ
  have h2 : (𝔓 ^ 2).map f ≤ 𝔓 ^ 2 := by
    rw [Ideal.map_pow]
    apply Ideal.pow_right_mono (by rw [Ideal.map_le_iff_le_comap]; intro z hz'; apply smul_mem_of_mem_inertia 𝔓 hσ hz') 2
  refine h2 (Ideal.mem_map_of_mem f hz)
private lemma pow_sub_pow_mem_sq (𝔓 : Ideal B) {a b : B} (hab : a - b ∈ 𝔓) {N : ℕ} (hN : (N : B) ∈ 𝔓) : a ^ N - b ^ N ∈ 𝔓 ^ 2 := by
  set m := a - b with hm
  have ha : a = b + m := by rw [hm]; ring
  rw [ha, add_pow, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, mul_one,
    add_sub_cancel_right]
  refine Ideal.sum_mem _ fun k hk => ?_
  rw [Finset.mem_range] at hk
  obtain hlt | hge := Nat.lt_or_ge (N - k) 2
  ·
    have hk1 : N - k = 1 := by omega
    have hkN : k = N - 1 := by omega
    have hch : (N.choose k : B) = N := by
      rw [hkN, Nat.choose_symm (by omega : 1 ≤ N), Nat.choose_one_right]
    rw [hk1, pow_one, hch, pow_two]
    apply Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ hab) hN
  ·
    have : m ^ (N - k) ∈ 𝔓 ^ 2 := by
      obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hge
      rw [hj, pow_add]
      apply Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hab 2)
    apply Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ this)
private lemma smul_sub_mem_sq_of_mem_inertia (𝔓 : Ideal B) [𝔓.IsMaximal] [Finite (B ⧸ 𝔓)] {ϖ : B} (hϖP : ϖ ∈ 𝔓) (hϖ : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) {σ : G} (hσ : σ ∈ 𝔓.inertia G) (hσϖ : σ • ϖ - ϖ ∈ 𝔓 ^ 2) (x : B) : σ • x - x ∈ 𝔓 ^ 2 := by
  classical
  let _ : Field (B ⧸ 𝔓) := Ideal.Quotient.field 𝔓
  let _ : Fintype (B ⧸ 𝔓) := Fintype.ofFinite _
  set N := Fintype.card (B ⧸ 𝔓) with hNdef
  have hN : (N : B) ∈ 𝔓 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, hNdef]
    apply Nat.cast_card_eq_zero (B ⧸ 𝔓)
  have hF : x ^ N - x ∈ 𝔓 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hNdef, FiniteField.pow_card, sub_self]
  obtain ⟨y, hy⟩ := hϖ (x - x ^ N) (by rw [← neg_sub]; apply 𝔓.neg_mem hF)
  set e := x - x ^ N - ϖ * y with he
  have hx : x = x ^ N + ϖ * y + e := by rw [he]; ring
  have h1 : σ • (x ^ N) - x ^ N ∈ 𝔓 ^ 2 := by
    rw [smul_pow']
    apply pow_sub_pow_mem_sq 𝔓 (hσ x) hN
  have h2 : σ • (ϖ * y) - ϖ * y ∈ 𝔓 ^ 2 := by
    have : σ • (ϖ * y) - ϖ * y = (σ • ϖ - ϖ) * (σ • y) + ϖ * (σ • y - y) := by
      rw [smul_mul']; ring
    rw [this]
    refine 𝔓 ^ 2 |>.add_mem (Ideal.mul_mem_right _ _ hσϖ) ?_
    rw [pow_two]
    apply Ideal.mul_mem_mul hϖP (hσ y)
  have h3 : σ • e - e ∈ 𝔓 ^ 2 := (𝔓 ^ 2).sub_mem (smul_mem_sq_of_mem_inertia 𝔓 hσ hy) hy
  have : σ • x - x = (σ • (x ^ N) - x ^ N) + (σ • (ϖ * y) - ϖ * y) + (σ • e - e) := by
    conv_lhs => rw [hx]
    rw [smul_add, smul_add]; ring
  rw [this]
  apply (𝔓 ^ 2).add_mem ((𝔓 ^ 2).add_mem h1 h2) h3
end

section

variable {B : Type u} [CommRing B] {G : Type v} [Group G] [MulSemiringAction G B]
variable (𝔓 : Ideal B)
variable {ϖ : B}
private lemma exists_tameCoeff (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) {σ : G} (hσ : σ ∈ 𝔓.inertia G) : ∃ t : B, σ • ϖ - ϖ * t ∈ 𝔓 ^ 2 :=
  hgen (σ • ϖ) (smul_mem_of_mem_inertia 𝔓 hσ hϖP)
private noncomputable def tameCoeff (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) {σ : G} (hσ : σ ∈ 𝔓.inertia G) : B := (exists_tameCoeff 𝔓 hϖP hgen hσ).choose
private lemma tameCoeff_spec (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) {σ : G} (hσ : σ ∈ 𝔓.inertia G) : σ • ϖ - ϖ * tameCoeff 𝔓 hϖP hgen hσ ∈ 𝔓 ^ 2 :=
  (exists_tameCoeff 𝔓 hϖP hgen hσ).choose_spec
private lemma tameCoeff_unique (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓) {z t t' : B} (ht : z - ϖ * t ∈ 𝔓 ^ 2) (ht' : z - ϖ * t' ∈ 𝔓 ^ 2) : t - t' ∈ 𝔓 := by
  apply hreg
  have : (t - t') * ϖ = (z - ϖ * t') - (z - ϖ * t) := by ring
  rw [this]
  apply (𝔓 ^ 2).sub_mem ht' ht
variable [𝔓.IsMaximal]
private lemma tameCoeff_not_mem (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓) {σ : G} (hσ : σ ∈ 𝔓.inertia G) : tameCoeff 𝔓 hϖP hgen hσ ∉ 𝔓 := by
  intro ht
  have h1 : σ • ϖ ∈ 𝔓 ^ 2 := by
    have h := tameCoeff_spec 𝔓 hϖP hgen hσ
    have h2 : ϖ * tameCoeff 𝔓 hϖP hgen hσ ∈ 𝔓 ^ 2 := by
      rw [pow_two]; apply Ideal.mul_mem_mul hϖP ht
    have : σ • ϖ = (σ • ϖ - ϖ * tameCoeff 𝔓 hϖP hgen hσ) + ϖ * tameCoeff 𝔓 hϖP hgen hσ := by ring
    rw [this]; apply (𝔓 ^ 2).add_mem h h2
  have h2 : ϖ ∈ 𝔓 ^ 2 := by
    have := smul_mem_sq_of_mem_inertia 𝔓 (Subgroup.inv_mem _ hσ) h1
    rwa [inv_smul_smul] at this
  apply Ideal.IsPrime.one_notMem (by infer_instance) (hreg 1 (by rwa [one_mul])) |> absurd <| by trivial
private noncomputable def tameCharFun (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓) (σ : 𝔓.inertia G) : Units (B ⧸ 𝔓) :=
  let _ : Field (B ⧸ 𝔓) := Ideal.Quotient.field 𝔓
  Units.mk0 (Ideal.Quotient.mk 𝔓 (tameCoeff 𝔓 hϖP hgen σ.2))
    (by rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; apply tameCoeff_not_mem 𝔓 hϖP hgen hreg σ.2)
private lemma val_tameCharFun (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓) (σ : 𝔓.inertia G) : ((tameCharFun 𝔓 hϖP hgen hreg σ : Units (B ⧸ 𝔓)) : B ⧸ 𝔓) = Ideal.Quotient.mk 𝔓 (tameCoeff 𝔓 hϖP hgen σ.2) := rfl
private noncomputable def tameChar (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓) : 𝔓.inertia G →* Units (B ⧸ 𝔓) where
  toFun := tameCharFun 𝔓 hϖP hgen hreg
  map_one' := by
    apply Units.ext
    rw [val_tameCharFun, Units.val_one, ← map_one (Ideal.Quotient.mk 𝔓), Ideal.Quotient.eq]
    refine tameCoeff_unique 𝔓 hreg (tameCoeff_spec 𝔓 hϖP hgen _) ?_
    simp
  map_mul' := by
    intro σ τ
    apply Units.ext
    rw [Units.val_mul, val_tameCharFun, val_tameCharFun, val_tameCharFun, ← map_mul, Ideal.Quotient.eq]
    refine tameCoeff_unique 𝔓 hreg (tameCoeff_spec 𝔓 hϖP hgen _) ?_
    set tσ := tameCoeff 𝔓 hϖP hgen σ.2
    set tτ := tameCoeff 𝔓 hϖP hgen τ.2
    have hτ := tameCoeff_spec 𝔓 hϖP hgen τ.2
    have hσ := tameCoeff_spec 𝔓 hϖP hgen σ.2
    have e1 : ((σ * τ : 𝔓.inertia G) : G) • ϖ = (σ : G) • ((τ : G) • ϖ) := mul_smul _ _ _
    have e2 : (σ : G) • ((τ : G) • ϖ) = (σ : G) • ((τ : G) • ϖ - ϖ * tτ) + ((σ : G) • ϖ) * ((σ : G) • tτ) := by
      rw [← smul_mul', ← smul_add]; congr 1; ring
    have hA : (σ : G) • ((τ : G) • ϖ - ϖ * tτ) ∈ 𝔓 ^ 2 := smul_mem_sq_of_mem_inertia 𝔓 σ.2 hτ
    have e3 : ((σ : G) • ϖ) * ((σ : G) • tτ) - ϖ * (tσ * tτ)
      = ((σ : G) • ϖ - ϖ * tσ) * ((σ : G) • tτ) + ϖ * (tσ * ((σ : G) • tτ - tτ)) := by ring
    have hB : ((σ : G) • ϖ) * ((σ : G) • tτ) - ϖ * (tσ * tτ) ∈ 𝔓 ^ 2 := by
      rw [e3]
      refine (𝔓 ^ 2).add_mem (Ideal.mul_mem_right _ _ hσ) ?_
      rw [pow_two]
      apply Ideal.mul_mem_mul hϖP (Ideal.mul_mem_left _ _ (σ.2 tτ))
    rw [e1, e2]
    have : (σ : G) • ((τ : G) • ϖ - ϖ * tτ) + ((σ : G) • ϖ) * ((σ : G) • tτ) - ϖ * (tσ * tτ)
      = (σ : G) • ((τ : G) • ϖ - ϖ * tτ) + (((σ : G) • ϖ) * ((σ : G) • tτ) - ϖ * (tσ * tτ)) := by ring
    rw [this]
    apply (𝔓 ^ 2).add_mem hA hB
variable (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2)
  (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓)
private lemma tameChar_apply (σ : 𝔓.inertia G) : ((tameChar (G := G) 𝔓 hϖP hgen hreg σ : Units (B ⧸ 𝔓)) : B ⧸ 𝔓) = Ideal.Quotient.mk 𝔓 (tameCoeff 𝔓 hϖP hgen σ.2) := rfl
private lemma tameChar_eq_one_iff (σ : 𝔓.inertia G) : tameChar 𝔓 hϖP hgen hreg σ = 1 ↔ (σ : G) • ϖ - ϖ ∈ 𝔓 ^ 2 := by
  rw [← Units.val_eq_one, tameChar_apply, ← map_one (Ideal.Quotient.mk 𝔓), Ideal.Quotient.eq]
  constructor
  ·
    intro h
    have hs := tameCoeff_spec 𝔓 hϖP hgen σ.2
    have : (σ : G) • ϖ - ϖ = ((σ : G) • ϖ - ϖ * tameCoeff 𝔓 hϖP hgen σ.2) + ϖ * (tameCoeff 𝔓 hϖP hgen σ.2 - 1) := by
      ring
    rw [this]
    refine (𝔓 ^ 2).add_mem hs ?_
    rw [pow_two]; apply Ideal.mul_mem_mul hϖP h
  ·
    intro h
    apply tameCoeff_unique 𝔓 hreg (tameCoeff_spec 𝔓 hϖP hgen σ.2) (by rwa [mul_one])
private lemma tameChar_eq_one_iff_forall [Finite (B ⧸ 𝔓)] (σ : 𝔓.inertia G) : tameChar 𝔓 hϖP hgen hreg σ = 1 ↔ ∀ x : B, (σ : G) • x - x ∈ 𝔓 ^ 2 := by
  rw [tameChar_eq_one_iff]
  exact ⟨fun h x => smul_sub_mem_sq_of_mem_inertia 𝔓 hϖP hgen σ.2 h x, fun h => h ϖ⟩
private lemma isCyclic_range_tameChar [Finite (B ⧸ 𝔓)] : IsCyclic (tameChar (G := G) 𝔓 hϖP hgen hreg).range := by
  let _ : Field (B ⧸ 𝔓) := Ideal.Quotient.field 𝔓
  apply isCyclic_of_injective_ringHom ((Units.coeHom (B ⧸ 𝔓)).comp (tameChar (G := G) 𝔓 hϖP hgen hreg).range.subtype)
    (Units.val_injective.comp Subtype.val_injective)
end

section

variable {B : Type u} [CommRing B] {G : Type v} [Group G] [MulSemiringAction G B]
variable (𝔓 : Ideal B)
private lemma smul_sub_pow_mul_mem_pow_succ {σ : G} (hσ : σ ∈ 𝔓.inertia G) {t : B} (h1 : ∀ x ∈ 𝔓, σ • x - t * x ∈ 𝔓 ^ 2) (k : ℕ) : ∀ x ∈ 𝔓 ^ k, σ • x - t ^ k * x ∈ 𝔓 ^ (k + 1) := by
  refine Nat.rec (motive := fun k => ∀ x, x ∈ 𝔓 ^ k → σ • x - t ^ k * x ∈ 𝔓 ^ (k + 1)) ?_ ?_ k
  ·
    intro x hx
    rw [pow_zero, one_mul, Nat.zero_add, pow_one]
    apply hσ x
  ·
    intro k ih x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun y z hy hz => ?_)
    ·
      have e : σ • (a * b) - t ^ (k + 1) * (a * b) = (σ • a - t ^ k * a) * (σ • b) + t ^ k * a * (σ • b - t * b) := by
        rw [smul_mul']; ring
      rw [e]
      refine (𝔓 ^ (k + 1 + 1)).add_mem ?_ ?_
      ·
        rw [pow_succ]
        apply Ideal.mul_mem_mul (ih a ha) (smul_mem_of_mem_inertia 𝔓 hσ hb)
      ·
        have : t ^ k * a * (σ • b - t * b) ∈ 𝔓 ^ k * 𝔓 ^ 2 :=
          Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ ha) (h1 b hb)
        rw [← pow_add] at this
        apply this
    ·
      have e : σ • (y + z) - t ^ (k + 1) * (y + z) = (σ • y - t ^ (k + 1) * y) + (σ • z - t ^ (k + 1) * z) := by
        rw [smul_add]; ring
      rw [e]; apply (𝔓 ^ (k + 1 + 1)).add_mem hy hz
private lemma smul_sub_mem_pow_succ_of_forall {σ : G} (hσ : σ ∈ 𝔓.inertia G) (h1 : ∀ x : B, σ • x - x ∈ 𝔓 ^ 2) (k : ℕ) {x : B} (hx : x ∈ 𝔓 ^ k) : σ • x - x ∈ 𝔓 ^ (k + 1) := by
  have := smul_sub_pow_mul_mem_pow_succ 𝔓 hσ (t := 1) (fun x _ => by rw [one_mul]; apply h1 x) k x hx
  rwa [one_pow, one_mul] at this
private lemma smul_sub_tameCoeff_mul_mem_sq [𝔓.IsMaximal] {ϖ : B} (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) {σ : G} (hσ : σ ∈ 𝔓.inertia G) {x : B} (hx : x ∈ 𝔓) : σ • x - tameCoeff 𝔓 hϖP hgen hσ * x ∈ 𝔓 ^ 2 := by
  set t := tameCoeff 𝔓 hϖP hgen hσ with ht
  have hs : σ • ϖ - ϖ * t ∈ 𝔓 ^ 2 := tameCoeff_spec 𝔓 hϖP hgen hσ
  obtain ⟨y, hy⟩ := hgen x hx
  set p₂ := x - ϖ * y with hp
  have hx' : x = ϖ * y + p₂ := by rw [hp]; ring
  have e : σ • x - t * x = (σ • ϖ - ϖ * t) * (σ • y) + t * ϖ * (σ • y - y) + (σ • p₂ - t * p₂) := by
    conv_lhs => rw [hx']
    rw [smul_add, smul_mul']; ring
  rw [e]
  refine (𝔓 ^ 2).add_mem ((𝔓 ^ 2).add_mem (Ideal.mul_mem_right _ _ hs) ?_) ?_
  ·
    rw [pow_two]
    apply Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ hϖP) (hσ y)
  · apply (𝔓 ^ 2).sub_mem (smul_mem_sq_of_mem_inertia 𝔓 hσ hy) (Ideal.mul_mem_left _ _ hy)
private lemma tameChar_pow_eq_one_of_smul_eq [𝔓.IsMaximal] {ϖ : B} (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓) (σ : 𝔓.inertia G) {k : ℕ} {α : B} (hαk : α ∈ 𝔓 ^ k) (hαreg : ∀ c : B, c * α ∈ 𝔓 ^ (k + 1) → c ∈ 𝔓) (hfix : (σ : G) • α = α) : tameChar 𝔓 hϖP hgen hreg σ ^ k = 1 := by
  let _ : Field (B ⧸ 𝔓) := Ideal.Quotient.field 𝔓
  set t := tameCoeff 𝔓 hϖP hgen σ.2 with ht
  have h := smul_sub_pow_mul_mem_pow_succ 𝔓 σ.2 (t := t)
    (fun x hx => smul_sub_tameCoeff_mul_mem_sq 𝔓 hϖP hgen σ.2 hx) k α hαk
  rw [hfix] at h
  have e1 : (1 - t ^ k) * α = α - t ^ k * α := by ring
  have h2 : (1 - t ^ k) ∈ 𝔓 := hαreg _ (by rw [e1]; apply h)
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, tameChar_apply, Units.val_one, ← map_pow, ← map_one (Ideal.Quotient.mk 𝔓),
    eq_comm, Ideal.Quotient.eq]
  apply h2
end

section

variable {B : Type u} [CommRing B] {G : Type v} [Group G] [MulSemiringAction G B]
variable (𝔓 : Ideal B)
private lemma smul_sub_mul_mem_sq_of_uniformizer {ϖ : B} (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) {σ : G} (hσ : σ ∈ 𝔓.inertia G) {t : B} (ht : σ • ϖ - ϖ * t ∈ 𝔓 ^ 2) {x : B} (hx : x ∈ 𝔓) : σ • x - t * x ∈ 𝔓 ^ 2 := by
  obtain ⟨y, hy⟩ := hgen x hx
  set p₂ := x - ϖ * y with hp
  have hx' : x = ϖ * y + p₂ := by rw [hp]; ring
  have e : σ • x - t * x = (σ • ϖ - ϖ * t) * (σ • y) + t * ϖ * (σ • y - y) + (σ • p₂ - t * p₂) := by
    conv_lhs => rw [hx']
    rw [smul_add, smul_mul']; ring
  rw [e]
  refine (𝔓 ^ 2).add_mem ((𝔓 ^ 2).add_mem (Ideal.mul_mem_right _ _ ht) ?_) ?_
  ·
    rw [pow_two]
    apply Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ hϖP) (hσ y)
  · apply (𝔓 ^ 2).sub_mem (smul_mem_sq_of_mem_inertia 𝔓 hσ hy) (Ideal.mul_mem_left _ _ hy)
private lemma smul_mem_sq_of_forall_smul_mem {φ : G} (hφP : ∀ x ∈ 𝔓, φ • x ∈ 𝔓) {z : B} (hz : z ∈ 𝔓 ^ 2) : φ • z ∈ 𝔓 ^ 2 := by
  let f : B →+* B := MulSemiringAction.toRingHom G B φ
  have h2 : (𝔓 ^ 2).map f ≤ 𝔓 ^ 2 := by
    rw [Ideal.map_pow]
    apply Ideal.pow_right_mono (by rw [Ideal.map_le_iff_le_comap]; intro x hx; apply hφP x hx) 2
  refine h2 (Ideal.mem_map_of_mem f hz)
private lemma conj_smul_sub_mul_pow_mem_sq {ϖ : B} (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) {σ : G} (hσ : σ ∈ 𝔓.inertia G) {t : B} (ht : σ • ϖ - ϖ * t ∈ 𝔓 ^ 2) {q : ℕ} {φ : G} (hφ : ∀ x : B, φ • x - x ^ q ∈ 𝔓) (hφP : ∀ x ∈ 𝔓, φ • x ∈ 𝔓) (hφP' : ∀ x ∈ 𝔓, φ⁻¹ • x ∈ 𝔓) : (φ * σ * φ⁻¹) • ϖ - ϖ * t ^ q ∈ 𝔓 ^ 2 := by
  set ϖ₁ := φ⁻¹ • ϖ with hϖ₁
  have hϖ₁P : ϖ₁ ∈ 𝔓 := hφP' ϖ hϖP
  have h1 : σ • ϖ₁ - t * ϖ₁ ∈ 𝔓 ^ 2 := smul_sub_mul_mem_sq_of_uniformizer 𝔓 hϖP hgen hσ ht hϖ₁P
  have h2 : φ • (σ • ϖ₁ - t * ϖ₁) ∈ 𝔓 ^ 2 := smul_mem_sq_of_forall_smul_mem 𝔓 hφP h1
  have e1 : (φ * σ * φ⁻¹) • ϖ = φ • (σ • ϖ₁) := by rw [hϖ₁, mul_smul, mul_smul]
  have e2 : φ • (σ • ϖ₁ - t * ϖ₁) = (φ * σ * φ⁻¹) • ϖ - (φ • t) * ϖ := by
    rw [smul_sub, smul_mul', e1, hϖ₁, smul_inv_smul]
  rw [e2] at h2
  have h3 : (φ • t) * ϖ - ϖ * t ^ q ∈ 𝔓 ^ 2 := by
    have : (φ • t) * ϖ - ϖ * t ^ q = (φ • t - t ^ q) * ϖ := by ring
    rw [this, pow_two]; apply Ideal.mul_mem_mul (hφ t) hϖP
  have : (φ * σ * φ⁻¹) • ϖ - ϖ * t ^ q = ((φ * σ * φ⁻¹) • ϖ - (φ • t) * ϖ) + ((φ • t) * ϖ - ϖ * t ^ q) := by ring
  rw [this]; apply (𝔓 ^ 2).add_mem h2 h3
private lemma exists_tameChar [𝔓.IsMaximal] [Finite (B ⧸ 𝔓)] {ϖ : B} (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓) : ∃ θ : 𝔓.inertia G →* Units (B ⧸ 𝔓), (∀ (σ : 𝔓.inertia G) (t : B), ((θ σ : Units (B ⧸ 𝔓)) : B ⧸ 𝔓) = Ideal.Quotient.mk 𝔓 t ↔ (σ : G) • ϖ - ϖ * t ∈ 𝔓 ^ 2) ∧ (∀ σ : 𝔓.inertia G, θ σ = 1 ↔ ∀ x : B, (σ : G) • x - x ∈ 𝔓 ^ 2) ∧ IsCyclic θ.range := by
  refine ⟨tameChar 𝔓 hϖP hgen hreg, fun σ t => ?_, fun σ => tameChar_eq_one_iff_forall 𝔓 hϖP hgen hreg σ,
    isCyclic_range_tameChar 𝔓 hϖP hgen hreg⟩
  rw [tameChar_apply, Ideal.Quotient.eq]
  constructor
  ·
    intro h
    have hs := tameCoeff_spec 𝔓 hϖP hgen σ.2
    have : (σ : G) • ϖ - ϖ * t = ((σ : G) • ϖ - ϖ * tameCoeff 𝔓 hϖP hgen σ.2) + ϖ * (tameCoeff 𝔓 hϖP hgen σ.2 - t) := by
      ring
    rw [this]
    refine (𝔓 ^ 2).add_mem hs ?_
    rw [pow_two]; apply Ideal.mul_mem_mul hϖP h
  ·
    intro h
    apply tameCoeff_unique 𝔓 hreg (tameCoeff_spec 𝔓 hϖP hgen σ.2) h
end

/--
[Ideal_exists_monoidHom_inertia_residueFieldUnits_ker_iff_of_uniformizer](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_exists_monoidHom_inertia_residueFieldUnits_ker_iff_of_uniformizer.lean)
-/
@[path]
private lemma main
  {B : Type u} {G : Type v} [CommRing B] [Group G]
  [MulSemiringAction G B] (𝔓 : Ideal B) [𝔓.IsMaximal] [Finite (B ⧸ 𝔓)] {ϖ : B} (hϖP : ϖ ∈ 𝔓)
  (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓) :
  -- imply
  ∃ θ : 𝔓.inertia G →* Units (B ⧸ 𝔓),
    (∀ (σ : 𝔓.inertia G) (t : B), ((θ σ : Units (B ⧸ 𝔓)) : B ⧸ 𝔓) = Ideal.Quotient.mk 𝔓 t ↔
      (σ : G) • ϖ - ϖ * t ∈ 𝔓 ^ 2) ∧
    (∀ σ : 𝔓.inertia G, θ σ = 1 ↔ ∀ x : B, (σ : G) • x - x ∈ 𝔓 ^ 2) ∧ IsCyclic θ.range :=
  exists_tameChar 𝔓 hϖP hgen hreg


-- created on 2026-10-20
