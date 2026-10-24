import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.Valuation.MaximalLattice
open DVRContext DVRContext.AnisotropicQuadSpace


/--
[form_smul_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/MaximalLattice.lean)
-/
@[path]
private lemma main
  {C : DVRContext}
  {C}
  {B : AnisotropicQuadSpace C}
  {r : C.k}
  {v w : Fin C.n → C.k} :
-- imply
  B.form v (r • w) = r * B.form v w := by
-- proof
  rw [B.form_symm, B.form_smul_left, B.form_symm]



/--
[form_add_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/MaximalLattice.lean)
-/
private lemma form_add_right
  {C : DVRContext}
  {C}
  {B : AnisotropicQuadSpace C}
  {u v w : Fin C.n → C.k} :
-- imply
  B.form u (v + w) = B.form u v + B.form u w := by
-- proof
  rw [B.form_symm, B.form_add_left, B.form_symm v, B.form_symm w]



/--
[form_zero_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/MaximalLattice.lean)
-/
private lemma form_zero_left
  {C : DVRContext}
  {C}
  {B : AnisotropicQuadSpace C}
  {v : Fin C.n → C.k} :
-- imply
  B.form 0 v = 0 := by
-- proof
  have h : (0 : Fin C.n → C.k) = (0 : C.k) • v := by
    ext i; simp [Pi.smul_apply, smul_eq_mul]
  rw [h, B.form_smul_left, zero_mul]



/--
[form_zero_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/MaximalLattice.lean)
-/
private lemma form_zero_right
  {C : DVRContext}
  {C}
  {B : AnisotropicQuadSpace C}
  {v : Fin C.n → C.k} :
-- imply
  B.form v 0 = 0 := by
-- proof
  rw [B.form_symm, form_zero_left]



/--
[form_add_expand](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/MaximalLattice.lean)
-/
private lemma form_add_expand
  {C : DVRContext}
  {C}
  {B : AnisotropicQuadSpace C}
  {x y : Fin C.n → C.k} :
-- imply
  B.form (x + y) (x + y) = B.form x x + 2 * B.form x y + B.form y y := by
-- proof
  rw [B.form_add_left, form_add_right, form_add_right]
  rw [B.form_symm y x]; ring



/--
[form_smul_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/MaximalLattice.lean)
-/
private lemma form_smul_self
  {C : DVRContext}
  {C}
  {B : AnisotropicQuadSpace C}
  {r : C.k}
  {x : Fin C.n → C.k} :
-- imply
  B.form (r • x) (r • x) = r * r * B.form x x := by
-- proof
  rw [B.form_smul_left, form_smul_right, mul_assoc]



/--
[two_unit_o](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/MaximalLattice.lean)
-/
private lemma two_unit_o
  {C : DVRContext}
  {C}
  {B : AnisotropicQuadSpace C}
  {B : AnisotropicQuadSpace C} :
-- imply
  IsUnit (2 : C.𝔬) := by
-- proof
  have h := B.two_unit
  change ∃ r : C.𝔬, IsUnit r ∧ C.embed r = 2 at h
  obtain ⟨r, hr_unit, hr_eq⟩ := h
  have h1 : C.embed r = C.embed (2 : C.𝔬) := by simp [hr_eq, map_ofNat]
  exact (C.embed_injective h1) ▸ hr_unit



/--
[hensel_quadratic_root](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/MaximalLattice.lean)
-/
private lemma hensel_quadratic_root
  {C : DVRContext}
  {C}
  {B : AnisotropicQuadSpace C}
  {B : AnisotropicQuadSpace C}
  {b c : C.k}
-- given
  (hb : C.isUnitInO b)
  (hc : C.isInMaxIdeal c) :
-- imply
  ∃ α : C.k, C.isInO α ∧ α * α + 2 * b * α + c = 0 := by
-- proof
  change ∃ r : C.𝔬, IsUnit r ∧ C.embed r = b at hb
  change ∃ r : C.𝔬, r ∈ C.maxIdeal ∧ C.embed r = c at hc
  obtain ⟨b_o, hb_unit, hb_eq⟩ := hb
  obtain ⟨c_o, hc_mem, hc_eq⟩ := hc
  haveI := B.inst_henselian
  set f := Polynomial.X ^ 2 + Polynomial.C (2 * b_o) * Polynomial.X + Polynomial.C c_o with hf_def
  have hf_assoc : f = Polynomial.X ^ 2 +
    (Polynomial.C (2 * b_o) * Polynomial.X + Polynomial.C c_o) := by
    rw [hf_def]; ring
  have hmonic : f.Monic := by
    rw [hf_assoc]
    apply Polynomial.monic_X_pow_add
    calc Polynomial.degree (Polynomial.C (2 * b_o) * Polynomial.X + Polynomial.C c_o)
      ≤ max (Polynomial.degree (Polynomial.C (2 * b_o) * Polynomial.X))
        (Polynomial.degree (Polynomial.C c_o)) := Polynomial.degree_add_le _ _
      _ ≤ max 1 0 := max_le_max (Polynomial.degree_C_mul_X_le _) Polynomial.degree_C_le
      _ = 1 := by simp
      _ < 2 := by norm_cast
  have hf0 : f.eval 0 = c_o := by
    simp [hf_def, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
  have hf'0 : (Polynomial.derivative f).eval 0 = 2 * b_o := by
    simp [hf_def, Polynomial.derivative_add, Polynomial.derivative_pow,
      Polynomial.derivative_X, Polynomial.derivative_C, Polynomial.derivative_mul,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
  have hf'0_unit : IsUnit ((Polynomial.derivative f).eval 0) := by
    rw [hf'0]; exact B.two_unit_o.mul hb_unit
  rw [B.hmax] at hc_mem
  have hf0_mem : f.eval 0 ∈ IsLocalRing.maximalIdeal C.𝔬 := by rwa [hf0]
  obtain ⟨a, ha_root, _⟩ := HenselianLocalRing.is_henselian f hmonic 0 hf0_mem hf'0_unit
  use C.embed a
  constructor
  · exact ⟨a, rfl⟩
  ·
    rw [Polynomial.IsRoot] at ha_root
    simp only [hf_def, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C] at ha_root
    have h_ring : a * a + 2 * b_o * a + c_o = 0 := by ring_nf; ring_nf at ha_root; exact ha_root
    have := congr_arg C.embed h_ring
    simp only [map_add, map_mul, map_zero, map_ofNat] at this
    rwa [hb_eq, hc_eq] at this



/--
[form_cross_integral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/MaximalLattice.lean)
-/
private lemma form_cross_integral
  {C : DVRContext}
  {C}
  {B : AnisotropicQuadSpace C}
  [DVRClosure C]
  {x y : Fin C.n → C.k}
-- given
  (hx : C.isInO (B.form x x))
  (hy : C.isInO (B.form y y)) :
-- imply
  C.isInO (B.form x y) := by
-- proof
  by_cases hx_zero : x = 0
  · rw [hx_zero, B.form_zero_left]; exact DVRClosure.isInO_zero
  have hxx_ne : B.form x x ≠ 0 := fun h => hx_zero (B.anisotropic x h)
  by_contra hxy_neg
  have hy_ne : y ≠ 0 := by
    intro h; exact hxy_neg (by rw [h, B.form_zero_right]; exact DVRClosure.isInO_zero)
  obtain ⟨n, hn_pos, hb_unit, hc_maxideal⟩ :=
    B.dvr_normalize_ratio (B.form x y) (B.form x x) hxy_neg hx hxx_ne
  set pi := C.embed C.uniformizer
  set b := pi ^ n * (B.form x y * (B.form x x)⁻¹)
  set c := pi ^ (2 * n) * (B.form y y * (B.form x x)⁻¹)
  obtain ⟨α, hα_inO, hα_root⟩ := B.hensel_quadratic_root b c hb_unit (hc_maxideal _ hy)
  set w := (α • x : Fin C.n → C.k) + (pi ^ n • y : Fin C.n → C.k)
  have hw_form : B.form w w = B.form x x * (α * α + 2 * b * α + c) := by
    show B.form (α • x + pi ^ n • y) (α • x + pi ^ n • y) =
      B.form x x * (α * α + 2 * b * α + c)
    rw [B.form_add_expand, B.form_smul_self, B.form_smul_self]
    rw [B.form_smul_left, B.form_smul_right]
    show α * α * B.form x x + 2 * (α * (pi ^ n * B.form x y)) +
      pi ^ n * (pi ^ n) * B.form y y =
      B.form x x * (α * α + 2 * (pi ^ n * (B.form x y * (B.form x x)⁻¹)) * α +
        pi ^ (2 * n) * (B.form y y * (B.form x x)⁻¹))
    have hxx_inv : B.form x x * (B.form x x)⁻¹ = 1 := by
      exact mul_inv_cancel₀ hxx_ne
    have hpow : pi ^ n * pi ^ n = pi ^ (2 * n) := by
      rw [← pow_add]; ring_nf
    field_simp
    ring
  have hw_zero : B.form w w = 0 := by rw [hw_form, hα_root, mul_zero]
  have hw_eq_zero : w = 0 := B.anisotropic w hw_zero
  have hcomp : ∀ i, α * x i + pi ^ n * y i = 0 := by
    intro i
    have : (α • x + pi ^ n • y) i = (0 : Fin C.n → C.k) i := by
      exact congr_fun hw_eq_zero i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    exact this
  by_cases hα_zero : α = 0
  ·
    have : y = 0 := by
      ext i
      have := hcomp i
      rw [hα_zero, zero_mul, zero_add] at this
      exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero n B.embed_pi_ne_zero)
    exact hy_ne this
  ·
    have hprop : x = (-(pi ^ n * α⁻¹)) • y := by
      ext i
      have hi := hcomp i
      have hα_mul : α * x i = -(pi ^ n * y i) := eq_neg_of_add_eq_zero_left hi
      have : x i = -(pi ^ n * α⁻¹) * y i := by
        have h1 := hα_mul
        have h2 : x i = α⁻¹ * (α * x i) := by
          rw [← mul_assoc, inv_mul_cancel₀ hα_zero, one_mul]
        rw [h1] at h2
        rw [h2]; ring
      simp [Pi.smul_apply, smul_eq_mul, this]
    have hxy_eq : B.form x y = -(pi ^ n * α⁻¹) * B.form y y := by
      conv_lhs => rw [hprop]
      rw [B.form_smul_left]
    have hxx_eq : B.form x x = (-(pi ^ n * α⁻¹)) * (-(pi ^ n * α⁻¹)) * B.form y y := by
      conv_lhs => rw [hprop]
      rw [B.form_smul_self]
    have hxy_sq : B.form x y * B.form x y = B.form x x * B.form y y := by
      rw [hxy_eq, hxx_eq]; ring
    have hxy_sq_inO : C.isInO (B.form x y * B.form x y) := by
      rw [hxy_sq]; exact DVRClosure.isInO_mul hx hy
    exact hxy_neg (B.dvr_sq_integral (B.form x y) hxy_sq_inO)



/--
[integralCarrier_add_closed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/MaximalLattice.lean)
-/
private lemma integralCarrier_add_closed
  {C : DVRContext}
  {C}
  {B : AnisotropicQuadSpace C}
  [DVRClosure C]
  {x y : Fin C.n → C.k}
-- given
  (hx : x ∈ B.integralCarrier)
  (hy : y ∈ B.integralCarrier) :
-- imply
  x + y ∈ B.integralCarrier := by
-- proof
  simp only [integralCarrier, Set.mem_setOf_eq] at hx hy ⊢
  rw [B.form_add_expand]
  have hxy := B.form_cross_integral x y hx hy
  exact DVRClosure.isInO_add
    (DVRClosure.isInO_add hx
      (DVRClosure.isInO_mul (by exact B.two_unit.elim fun r ⟨hr, he⟩ => ⟨r, he⟩) hxy))
    hy



/--
[integralCarrier_zero_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/MaximalLattice.lean)
-/
private lemma integralCarrier_zero_mem
  {C : DVRContext}
  {C}
  {B : AnisotropicQuadSpace C}
  [DVRClosure C] :
-- imply
  (0 : Fin C.n → C.k) ∈ B.integralCarrier := by
-- proof
  simp only [integralCarrier, Set.mem_setOf_eq, B.form_zero_left]
  exact DVRClosure.isInO_zero



/--
[integralCarrier_smul_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/MaximalLattice.lean)
-/
private lemma integralCarrier_smul_mem
  {C : DVRContext}
  {C}
  {B : AnisotropicQuadSpace C}
  [DVRClosure C]
  {r : C.𝔬}
  {v : Fin C.n → C.k}
-- given
  (hv : v ∈ B.integralCarrier) :
-- imply
  C.oscal r v ∈ B.integralCarrier := by
-- proof
  simp only [integralCarrier, Set.mem_setOf_eq] at hv ⊢
  have heq : C.oscal r v = C.embed r • v := by
    ext i; simp [DVRContext.oscal, Pi.smul_apply, smul_eq_mul]
  rw [heq, B.form_smul_self]
  exact DVRClosure.isInO_mul (DVRClosure.isInO_mul ⟨r, rfl⟩ ⟨r, rfl⟩) hv



/--
[oValued_subset_integralCarrier](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/MaximalLattice.lean)
-/
private lemma oValued_subset_integralCarrier
  {C : DVRContext}
  {C}
  {B : AnisotropicQuadSpace C}
  {Λ : C.OLattice}
-- given
  (hΛ : B.IsOValued Λ) :
-- imply
  Λ.carrier ⊆ B.integralCarrier :=
-- proof
  fun _ hv => hΛ _ _ hv hv



/--
[unique_maximal_oValued_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/MaximalLattice.lean)
-/
private lemma unique_maximal_oValued_lattice
  {C : DVRContext}
  {C}
  {B : AnisotropicQuadSpace C}
  [DVRClosure C] :
-- imply
  (∀ x y : Fin C.n → C.k, x ∈ B.integralCarrier → y ∈ B.integralCarrier → x + y ∈ B.integralCarrier) ∧ ((0 : Fin C.n → C.k) ∈ B.integralCarrier) ∧ (∀ (r : C.𝔬) (v : Fin C.n → C.k), v ∈ B.integralCarrier → C.oscal r v ∈ B.integralCarrier) ∧ (∀ v w : Fin C.n → C.k, v ∈ B.integralCarrier → w ∈ B.integralCarrier → C.isInO (B.form v w)) ∧ (∀ (Λ : C.OLattice), B.IsOValued Λ → Λ.carrier ⊆ B.integralCarrier) :=
-- proof
  ⟨fun x y hx hy => B.integralCarrier_add_closed x y hx hy,
    B.integralCarrier_zero_mem,
    fun r v hv => B.integralCarrier_smul_mem r v hv,
    fun v w hv hw => B.form_cross_integral v w hv hw,
    fun Λ hΛ => B.oValued_subset_integralCarrier Λ hΛ⟩



-- created on 2026-10-23
-- updated on 2026-10-24
