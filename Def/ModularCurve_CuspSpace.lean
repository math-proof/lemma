module
public import Mathlib
open Matrix Matrix.SpecialLinearGroup OnePoint CongruenceSubgroup
open scoped MatrixGroups
set_option linter.defProp false


public section

namespace ModularCurve

noncomputable section

def ratPoint (a c : ℤ) : OnePoint ℚ :=
  if c = 0 then ∞ else (((a : ℚ) / (c : ℚ) : ℚ) : OnePoint ℚ)

variable (N : ℕ)

def Gamma0Q : Subgroup (GL (Fin 2) ℚ) := (Gamma0 N).map (mapGL ℚ)

abbrev CuspSpace : Type := MulAction.orbitRel.Quotient (Gamma0Q N) (OnePoint ℚ)

namespace CuspSpace

def mk (x : OnePoint ℚ) : CuspSpace N := ⟦x⟧

variable {N}

variable (N)

/-! `Def` must not depend on `Instance`/`Theorem`, so the facts needed to make
`fromCoset` and `cuspDenom` well defined are carried here as `private def`s
rather than imported. -/

private def mk_eq_mk_iff_aux {N : ℕ} {x y : OnePoint ℚ} :
    mk N x = mk N y ↔ ∃ γ ∈ Gamma0 N, mapGL ℚ γ • y = x := by
  rw [mk, mk, Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨g, γ, hγ, rfl⟩, hg⟩
    exact ⟨γ, hγ, hg⟩
  · rintro ⟨γ, hγ, hg⟩
    exact ⟨⟨mapGL ℚ γ, γ, hγ, rfl⟩, hg⟩

private def mk_smul_aux {N : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) (x : OnePoint ℚ) :
    mk N (mapGL ℚ γ • x) = mk N x :=
  mk_eq_mk_iff_aux.mpr ⟨_, hγ, rfl⟩

def fromCoset : SL(2, ℤ) ⧸ Gamma0 N → CuspSpace N :=
  Quotient.lift (fun g => mk N (mapGL ℚ g⁻¹ • ∞))
    (fun a b hab => by
      have hmem : a⁻¹ * b ∈ Gamma0 N := QuotientGroup.leftRel_apply.mp hab
      have key : mapGL ℚ b⁻¹ • (∞ : OnePoint ℚ)
          = mapGL ℚ (a⁻¹ * b)⁻¹ • (mapGL ℚ a⁻¹ • (∞ : OnePoint ℚ)) := by
        have h1 : (a⁻¹ * b)⁻¹ * a⁻¹ = b⁻¹ := by group
        rw [← mul_smul, ← map_mul, h1]
      rw [key]
      exact (mk_smul_aux (inv_mem hmem) _).symm)

def cuspDenomAux (x : OnePoint ℚ) : ℕ :=
  x.elim N fun q => Nat.gcd q.den N

variable {N}

@[simp] private def ratPoint_zero_right_aux (a : ℤ) : ratPoint a 0 = ∞ := if_pos rfl

private def ratPoint_of_ne_zero_aux (a : ℤ) {c : ℤ} (hc : c ≠ 0) :
    ratPoint a c = (((a : ℚ) / (c : ℚ) : ℚ) : OnePoint ℚ) := if_neg hc

private def ratPoint_mul_left_aux {l : ℤ} (hl : l ≠ 0) (a c : ℤ) :
    ratPoint (l * a) (l * c) = ratPoint a c := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · rw [ratPoint_of_ne_zero_aux _ (mul_ne_zero hl hc), ratPoint_of_ne_zero_aux _ hc]
    push_cast
    rw [mul_div_mul_left _ _ (by exact_mod_cast hl)]

private def exists_ratPoint_eq_aux (x : OnePoint ℚ) :
    ∃ a c : ℤ, IsCoprime a c ∧ ratPoint a c = x := by
  cases x with
  | infty => exact ⟨1, 0, isCoprime_one_left, rfl⟩
  | coe q =>
    refine ⟨q.num, (q.den : ℤ), ?_, ?_⟩
    · rw [Int.isCoprime_iff_gcd_eq_one]
      simpa [Int.gcd] using q.reduced
    · rw [ratPoint_of_ne_zero_aux _ (by exact_mod_cast q.den_nz), OnePoint.coe_eq_coe,
        show ((q.den : ℤ) : ℚ) = (q.den : ℚ) by push_cast; ring, Rat.num_div_den]

private def mapGL_apply_coe_aux (γ : SL(2, ℤ)) (i j : Fin 2) :
    (mapGL ℚ γ) i j = ((γ i j : ℤ) : ℚ) := by
  simp [mapGL]

private def mapGL_smul_infty_aux (γ : SL(2, ℤ)) :
    mapGL ℚ γ • (∞ : OnePoint ℚ) = ratPoint (γ 0 0) (γ 1 0) := by
  rw [smul_infty_eq_ite, mapGL_apply_coe_aux, mapGL_apply_coe_aux]
  rcases eq_or_ne (γ 1 0) 0 with h | h
  · simp [h]
  · rw [if_neg (by exact_mod_cast h), ratPoint_of_ne_zero_aux _ h]

private def mapGL_smul_ratPoint_aux (γ : SL(2, ℤ)) {a c : ℤ} (h : a ≠ 0 ∨ c ≠ 0) :
    mapGL ℚ γ • ratPoint a c =
      ratPoint (γ 0 0 * a + γ 0 1 * c) (γ 1 0 * a + γ 1 1 * c) := by
  rcases eq_or_ne c 0 with rfl | hc
  ·
    replace h : a ≠ 0 := h.resolve_right (by simp)
    rw [ratPoint_zero_right_aux, mapGL_smul_infty_aux]
    simp only [mul_zero, add_zero]
    rw [mul_comm (γ 0 0) a, mul_comm (γ 1 0) a, ratPoint_mul_left_aux h]
  ·
    rw [ratPoint_of_ne_zero_aux _ hc, smul_some_eq_ite]
    have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast hc
    have hden : (mapGL ℚ γ) 1 0 * ((a : ℚ) / c) + (mapGL ℚ γ) 1 1
        = (((γ 1 0 * a + γ 1 1 * c : ℤ) : ℚ)) / (c : ℚ) := by
      simp only [mapGL_apply_coe_aux]
      field_simp
      push_cast
      ring
    have hnum : (mapGL ℚ γ) 0 0 * ((a : ℚ) / c) + (mapGL ℚ γ) 0 1
        = (((γ 0 0 * a + γ 0 1 * c : ℤ) : ℚ)) / (c : ℚ) := by
      simp only [mapGL_apply_coe_aux]
      field_simp
      push_cast
      ring
    rcases eq_or_ne (γ 1 0 * a + γ 1 1 * c) 0 with h0 | h0
    · rw [if_pos (by rw [hden, h0]; simp), h0, ratPoint_zero_right_aux]
    · rw [if_neg (by rw [hden]; exact div_ne_zero (by exact_mod_cast h0) hcQ),
        ratPoint_of_ne_zero_aux _ h0, hnum, hden, OnePoint.coe_eq_coe,
        div_div_div_cancel_right₀ hcQ]

private def isCoprime_smul_pair_aux (γ : SL(2, ℤ)) {a c : ℤ} (h : IsCoprime a c) :
    IsCoprime (γ 0 0 * a + γ 0 1 * c) (γ 1 0 * a + γ 1 1 * c) := by
  have := IsCoprime.mulVecSL (v := ![a, c]) (by simpa using h) γ
  simpa [Matrix.mulVec_fin_two] using this

private def Gamma0_mem_iff_dvd_aux {N : ℕ} {γ : SL(2, ℤ)} :
    γ ∈ Gamma0 N ↔ (N : ℤ) ∣ γ 1 0 := by
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]

@[simp] private def cuspDenomAux_coe_aux (N : ℕ) (q : ℚ) :
    cuspDenomAux N (q : OnePoint ℚ) = Nat.gcd q.den N := rfl

private def cuspDenomAux_ratPoint_aux (N : ℕ) {a c : ℤ} (h : IsCoprime a c) :
    cuspDenomAux N (ratPoint a c) = Int.gcd c N := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [cuspDenomAux, Int.gcd]
  · rw [ratPoint_of_ne_zero_aux _ hc, cuspDenomAux_coe_aux]
    have hcop : Nat.Coprime a.natAbs c.natAbs := Int.isCoprime_iff_gcd_eq_one.mp h
    have hden : (((a : ℚ) / (c : ℚ)).den : ℤ) = (c.natAbs : ℤ) := by
      rcases lt_or_gt_of_ne hc with hneg | hpos
      · have : ((a : ℚ) / (c : ℚ)) = (((-a : ℤ) : ℚ) / ((-c : ℤ) : ℚ)) := by
          push_cast; rw [neg_div_neg_eq]
        rw [this, Rat.den_div_eq_of_coprime (by omega) (by simpa using hcop)]
        omega
      · rw [Rat.den_div_eq_of_coprime hpos hcop]
        omega
    have : ((a : ℚ) / (c : ℚ)).den = c.natAbs := by exact_mod_cast hden
    rw [this]
    rfl

private def cuspDenomAux_dvd_smul_aux (N : ℕ) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N)
    (x : OnePoint ℚ) :
    cuspDenomAux N x ∣ cuspDenomAux N (mapGL ℚ γ • x) := by
  obtain ⟨a, c, hac, rfl⟩ := exists_ratPoint_eq_aux x
  have hac' : a ≠ 0 ∨ c ≠ 0 := hac.ne_zero_or_ne_zero
  rw [mapGL_smul_ratPoint_aux γ hac', cuspDenomAux_ratPoint_aux N hac,
    cuspDenomAux_ratPoint_aux N (isCoprime_smul_pair_aux γ hac)]

  have h1 : (Int.gcd c N : ℤ) ∣ γ 1 0 * a + γ 1 1 * c := by
    refine dvd_add (Dvd.dvd.mul_right ?_ a) (Dvd.dvd.mul_left (Int.gcd_dvd_left ..) _)
    exact (Int.gcd_dvd_right ..).trans (Gamma0_mem_iff_dvd_aux.mp hγ)
  exact Int.dvd_gcd h1 (Int.gcd_dvd_right ..)

private def cuspDenomAux_smul_aux (N : ℕ) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N)
    (x : OnePoint ℚ) :
    cuspDenomAux N (mapGL ℚ γ • x) = cuspDenomAux N x := by
  refine Nat.dvd_antisymm ?_ (cuspDenomAux_dvd_smul_aux N hγ x)
  have := cuspDenomAux_dvd_smul_aux N (inv_mem hγ) (mapGL ℚ γ • x)
  rwa [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at this

variable (N)

def cuspDenom : CuspSpace N → ℕ :=
  Quotient.lift (cuspDenomAux N) (by
    rintro x y ⟨⟨g, γ, hγ, rfl⟩, rfl⟩
    exact cuspDenomAux_smul_aux N hγ y)

variable {N}

def NormalFormCriterion (N : ℕ) : Prop :=
  ∀ (a a' : ℤ) (e : ℕ), e ∣ N → IsCoprime a (e : ℤ) → IsCoprime a' (e : ℤ) →
    (mk N (ratPoint a e) = mk N (ratPoint a' e) ↔
      (a : ZMod (Nat.gcd e (N / e))) = (a' : ZMod (Nat.gcd e (N / e))))

def Classification (N : ℕ) : Prop :=
  Nonempty (CuspSpace N ≃ (d : N.divisors) × (ZMod (Nat.gcd d (N / (d : ℕ))))ˣ)

end CuspSpace

end

end ModularCurve

open Matrix Matrix.SpecialLinearGroup OnePoint CongruenceSubgroup

open scoped MatrixGroups

namespace ModularCurve

noncomputable section

def cuspWidthOfDenom (N d : ℕ) : ℕ := N / Nat.gcd (d ^ 2) N

namespace CuspSpace

variable {N : ℕ}

def cuspWidth (x : CuspSpace N) : ℕ := cuspWidthOfDenom N (cuspDenom N x)

end CuspSpace

end

end ModularCurve
