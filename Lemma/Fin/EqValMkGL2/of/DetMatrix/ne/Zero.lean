import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.Valuation.IwahoriDecomp
open Matrix DVRContext


/--
[mkGL2_val_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/IwahoriDecomp.lean)
-/
@[path]
private lemma main
  {C : DVRContext}
  [DVRClosureGL2 C]
  {C}
  {f : Fin 2 → Fin 2 → C.k}
  {i j : Fin 2}
-- given
  (hdet : (show Matrix (Fin 2) (Fin 2) C.k from f).det ≠ 0) :
-- imply
  (mkGL2 f hdet).val i j = f i j := by
-- proof
  simp only [mkGL2, unitOfDetInvertible]; rfl



/--
[iwahoriGL2Gen_eq_iwahoriGL2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/IwahoriDecomp.lean)
-/
private lemma iwahoriGL2Gen_eq_iwahoriGL2
  {C : DVRContext}
  [DVRClosureGL2 C]
  {C}
  (C) :
-- imply
  C.IwahoriGL2Gen = C.IwahoriGL2 := by
-- proof
  ext g
  simp only [IwahoriGL2Gen, IwahoriGL2, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hdiag, hupper, hlower⟩
    exact ⟨hdiag 0, hdiag 1, hupper 0 1 (by omega), hlower 1 0 (by omega)⟩
  · rintro ⟨h00, h11, h01, h10⟩
    refine ⟨fun i => ?_, fun i j hij => ?_, fun i j hij => ?_⟩
    · fin_cases i <;> assumption
    · fin_cases i <;> fin_cases j <;> simp_all
    · fin_cases i <;> fin_cases j <;> simp_all



/--
[lowerUnipGL2Gen_eq_lowerUnipGL2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/IwahoriDecomp.lean)
-/
private lemma lowerUnipGL2Gen_eq_lowerUnipGL2
  {C : DVRContext}
  [DVRClosureGL2 C]
  {C}
  (C) :
-- imply
  C.LowerUnipGL2Gen = C.LowerUnipGL2 := by
-- proof
  ext g
  simp only [LowerUnipGL2Gen, LowerUnipGL2, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hdiag, hupper⟩
    exact ⟨hdiag 0, hdiag 1, hupper 0 1 (by omega)⟩
  · rintro ⟨h00, h11, h01⟩
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · fin_cases i <;> assumption
    · fin_cases i <;> fin_cases j <;> simp_all



/--
[upperUnipGL2Gen_eq_upperUnipGL2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/IwahoriDecomp.lean)
-/
private lemma upperUnipGL2Gen_eq_upperUnipGL2
  {C : DVRContext}
  [DVRClosureGL2 C]
  {C}
  (C) :
-- imply
  C.UpperUnipGL2Gen = C.UpperUnipGL2 := by
-- proof
  ext g
  simp only [UpperUnipGL2Gen, UpperUnipGL2, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hdiag, hlower⟩
    exact ⟨hdiag 0, hdiag 1, hlower 1 0 (by omega)⟩
  · rintro ⟨h00, h11, h10⟩
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · fin_cases i <;> assumption
    · fin_cases i <;> fin_cases j <;> simp_all



/--
[diagGL2Gen_eq_diagGL2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/IwahoriDecomp.lean)
-/
private lemma diagGL2Gen_eq_diagGL2
  {C : DVRContext}
  [DVRClosureGL2 C]
  {C}
  (C) :
-- imply
  C.DiagGL2Gen = C.DiagGL2 := by
-- proof
  ext g
  simp only [DiagGL2Gen, DiagGL2, Set.mem_setOf_eq]
  constructor
  · intro h; exact ⟨h 0 1 (by omega), h 1 0 (by omega)⟩
  · rintro ⟨h01, h10⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all



/--
[isUnitInO_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/IwahoriDecomp.lean)
-/
private lemma isUnitInO_one
  {C : DVRContext}
  [DVRClosureGL2 C]
  {C}
  (C) :
-- imply
  C.isUnitInO (1 : C.k) :=
-- proof
  ⟨1, isUnit_one, C.embed.map_one⟩



/--
[isInMaxIdeal_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/IwahoriDecomp.lean)
-/
private lemma isInMaxIdeal_zero
  {C : DVRContext}
  [DVRClosureGL2 C]
  {C}
  (C) :
-- imply
  C.isInMaxIdeal (0 : C.k) :=
-- proof
  ⟨0, Ideal.zero_mem _, C.embed.map_zero⟩



/--
[gl2_triple_product_entry](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/IwahoriDecomp.lean)
-/
private lemma gl2_triple_product_entry
  {C : DVRContext}
  [DVRClosureGL2 C]
  {C}
  (C)
  {u' m u : GL (Fin 2) C.k}
  {i j : Fin 2}
-- given
  (hm01 : m.val 0 1 = 0)
  (hm10 : m.val 1 0 = 0) :
-- imply
  (u' * m * u).val i j = u'.val i 0 * m.val 0 0 * u.val 0 j + u'.val i 1 * m.val 1 1 * u.val 1 j := by
-- proof
  show (u'.val * m.val * u.val) i j = _
  simp only [mul_apply, Fin.sum_univ_two]
  rw [hm01, hm10]; ring



/--
[iwahori_decomp_gl2_exists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/IwahoriDecomp.lean)
-/
private lemma iwahori_decomp_gl2_exists
  {C : DVRContext}
  [DVRClosureGL2 C]
  {C}
  (C) :
-- imply
  ∀ b ∈ C.IwahoriGL2, ∃ (u' m u : GL (Fin 2) C.k), u' ∈ C.LowerUnipGL2 ∩ C.IwahoriGL2 ∧ m ∈ C.DiagGL2 ∩ C.IwahoriGL2 ∧ u ∈ C.UpperUnipGL2 ∩ C.IwahoriGL2 ∧ b = u' * m * u := by
-- proof
  intro b ⟨ha_unit, hd_unit, hβ_O, hc_m⟩
  set a := b.val 0 0
  set β := b.val 0 1
  set c := b.val 1 0
  set d := b.val 1 1
  have ha_ne : a ≠ 0 := DVRClosureGL2.isUnitInO_ne_zero ha_unit
  have ha_inv_O : C.isInO a⁻¹ := DVRClosure.isUnitInO_inv ha_unit
  have hca_inv_m : C.isInMaxIdeal (c * a⁻¹) :=
    DVRClosureGL2.isInMaxIdeal_mul_isInO hc_m ha_inv_O
  have ha_inv_β_O : C.isInO (a⁻¹ * β) := DVRClosure.isInO_mul ha_inv_O hβ_O
  have hcab_m : C.isInMaxIdeal (c * a⁻¹ * β) :=
    DVRClosureGL2.isInMaxIdeal_mul_isInO hca_inv_m hβ_O
  have hd_mid_unit : C.isUnitInO (d - c * a⁻¹ * β) :=
    DVRClosureGL2.isUnitInO_sub_isInMaxIdeal hd_unit hcab_m
  have hd_mid_ne : d - c * a⁻¹ * β ≠ 0 :=
    DVRClosureGL2.isUnitInO_ne_zero hd_mid_unit
  let u'_f : Fin 2 → Fin 2 → C.k := ![![1, 0], ![c * a⁻¹, 1]]
  have hu'_det : (show Matrix (Fin 2) (Fin 2) C.k from u'_f).det ≠ 0 := by
    rw [det_fin_two]; simp [u'_f]
  let m_f : Fin 2 → Fin 2 → C.k := ![![a, 0], ![0, d - c * a⁻¹ * β]]
  have hm_det : (show Matrix (Fin 2) (Fin 2) C.k from m_f).det ≠ 0 := by
    rw [det_fin_two]; simp [m_f]; exact ⟨ha_ne, hd_mid_ne⟩
  let u_f : Fin 2 → Fin 2 → C.k := ![![1, a⁻¹ * β], ![0, 1]]
  have hu_det : (show Matrix (Fin 2) (Fin 2) C.k from u_f).det ≠ 0 := by
    rw [det_fin_two]; simp [u_f]
  let u'_gl := mkGL2 u'_f hu'_det
  let m_gl := mkGL2 m_f hm_det
  let u_gl := mkGL2 u_f hu_det
  have hu'_e : u'_gl.val 0 0 = 1 ∧ u'_gl.val 0 1 = 0 ∧
    u'_gl.val 1 0 = c * a⁻¹ ∧ u'_gl.val 1 1 = 1 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [u'_gl, u'_f]
  have hm_e : m_gl.val 0 0 = a ∧ m_gl.val 0 1 = 0 ∧
    m_gl.val 1 0 = 0 ∧ m_gl.val 1 1 = d - c * a⁻¹ * β := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [m_gl, m_f]
  have hu_e : u_gl.val 0 0 = 1 ∧ u_gl.val 0 1 = a⁻¹ * β ∧
    u_gl.val 1 0 = 0 ∧ u_gl.val 1 1 = 1 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [u_gl, u_f]
  refine ⟨u'_gl, m_gl, u_gl, ?_, ?_, ?_, ?_⟩
  · exact ⟨⟨hu'_e.1, hu'_e.2.2.2, hu'_e.2.1⟩,
    hu'_e.1 ▸ C.isUnitInO_one,
    hu'_e.2.2.2 ▸ C.isUnitInO_one,
    hu'_e.2.1 ▸ DVRClosure.isInO_zero,
    hu'_e.2.2.1 ▸ hca_inv_m⟩
  · exact ⟨⟨hm_e.2.1, hm_e.2.2.1⟩,
    hm_e.1 ▸ ha_unit,
    hm_e.2.2.2 ▸ hd_mid_unit,
    hm_e.2.1 ▸ DVRClosure.isInO_zero,
    hm_e.2.2.1 ▸ C.isInMaxIdeal_zero⟩
  · exact ⟨⟨hu_e.1, hu_e.2.2.2, hu_e.2.2.1⟩,
    hu_e.1 ▸ C.isUnitInO_one,
    hu_e.2.2.2 ▸ C.isUnitInO_one,
    hu_e.2.1 ▸ ha_inv_β_O,
    hu_e.2.2.1 ▸ C.isInMaxIdeal_zero⟩
  · apply Units.val_injective
    ext i j
    show b.val i j = (u'_gl * m_gl * u_gl).val i j
    rw [gl2_triple_product_entry C u'_gl m_gl u_gl hm_e.2.1 hm_e.2.2.1]
    fin_cases i <;> fin_cases j <;> dsimp
    · rw [hu'_e.1, hu'_e.2.1, hu_e.1, hu_e.2.2.1, hm_e.1, hm_e.2.2.2]; ring
    · rw [hu'_e.1, hu'_e.2.1, hu_e.2.1, hu_e.2.2.2, hm_e.1, hm_e.2.2.2]
      simp only [one_mul, mul_one, zero_mul, mul_zero, add_zero]
      rw [mul_inv_cancel_left₀ ha_ne]
    · rw [hu'_e.2.2.1, hu'_e.2.2.2, hu_e.1, hu_e.2.2.1, hm_e.1, hm_e.2.2.2]
      simp only [one_mul, mul_one, zero_mul, mul_zero, add_zero]
      rw [inv_mul_cancel_right₀ ha_ne]
    · rw [hu'_e.2.2.1, hu'_e.2.2.2, hu_e.2.1, hu_e.2.2.2, hm_e.1, hm_e.2.2.2]
      simp only [one_mul, mul_one]
      rw [inv_mul_cancel_right₀ ha_ne, mul_assoc]
      exact (add_sub_cancel (c * (a⁻¹ * β)) d).symm



/--
[iwahori_decomp_gl2_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/IwahoriDecomp.lean)
-/
private lemma iwahori_decomp_gl2_unique
  {C : DVRContext}
  [DVRClosureGL2 C]
  {C}
  (C) :
-- imply
  ∀ b ∈ C.IwahoriGL2, ∀ (t₁ t₂ : GL (Fin 2) C.k × GL (Fin 2) C.k × GL (Fin 2) C.k), (t₁.1 ∈ C.LowerUnipGL2 ∩ C.IwahoriGL2 ∧ t₁.2.1 ∈ C.DiagGL2 ∩ C.IwahoriGL2 ∧ t₁.2.2 ∈ C.UpperUnipGL2 ∩ C.IwahoriGL2 ∧ b = t₁.1 * t₁.2.1 * t₁.2.2) → (t₂.1 ∈ C.LowerUnipGL2 ∩ C.IwahoriGL2 ∧ t₂.2.1 ∈ C.DiagGL2 ∩ C.IwahoriGL2 ∧ t₂.2.2 ∈ C.UpperUnipGL2 ∩ C.IwahoriGL2 ∧ b = t₂.1 * t₂.2.1 * t₂.2.2) → t₁ = t₂ := by
-- proof
  intro b _hb ⟨u'₁, m₁, u₁⟩ ⟨u'₂, m₂, u₂⟩ h₁ h₂
  simp only [Prod.fst, Prod.snd] at h₁ h₂
  obtain ⟨⟨⟨hu'₁_00, hu'₁_11, hu'₁_01⟩, _⟩,
    ⟨⟨hm₁_01, hm₁_10⟩, hm₁_iwa⟩,
    ⟨⟨hu₁_00, hu₁_11, hu₁_10⟩, _⟩, heq₁⟩ := h₁
  obtain ⟨⟨⟨hu'₂_00, hu'₂_11, hu'₂_01⟩, _⟩,
    ⟨⟨hm₂_01, hm₂_10⟩, _⟩,
    ⟨⟨hu₂_00, hu₂_11, hu₂_10⟩, _⟩, heq₂⟩ := h₂
  have h_eq : u'₁ * m₁ * u₁ = u'₂ * m₂ * u₂ := by rw [← heq₁, ← heq₂]
  have h_entry : ∀ i j : Fin 2,
    (u'₁ * m₁ * u₁).val i j = (u'₂ * m₂ * u₂).val i j := by
    intro i j; rw [h_eq]
  have p₁ := gl2_triple_product_entry C u'₁ m₁ u₁ hm₁_01 hm₁_10
  have p₂ := gl2_triple_product_entry C u'₂ m₂ u₂ hm₂_01 hm₂_10
  have hm00_ne : m₁.val 0 0 ≠ 0 := DVRClosureGL2.isUnitInO_ne_zero hm₁_iwa.1
  have hm00 : m₁.val 0 0 = m₂.val 0 0 := by
    have := h_entry 0 0; rw [p₁, p₂] at this
    rw [hu'₁_00, hu'₁_01, hu₁_00, hu₁_10,
      hu'₂_00, hu'₂_01, hu₂_00, hu₂_10] at this
    ring_nf at this; exact this
  have hu01 : u₁.val 0 1 = u₂.val 0 1 := by
    have := h_entry 0 1; rw [p₁, p₂] at this
    rw [hu'₁_00, hu'₁_01, hu₁_11,
      hu'₂_00, hu'₂_01, hu₂_11] at this
    simp only [one_mul, mul_one, zero_mul, mul_zero, add_zero] at this
    rw [hm00] at this
    have hm₂_ne : (↑m₂ : Matrix (Fin 2) (Fin 2) C.k) 0 0 ≠ 0 := hm00 ▸ hm00_ne
    exact mul_left_cancel₀ hm₂_ne this
  have hu'10 : u'₁.val 1 0 = u'₂.val 1 0 := by
    have := h_entry 1 0; rw [p₁, p₂] at this
    rw [hu'₁_11, hu₁_00, hu₁_10,
      hu'₂_11, hu₂_00, hu₂_10] at this
    simp only [one_mul, mul_one, zero_mul, mul_zero, add_zero] at this
    rw [hm00] at this
    have hm₂_ne : (↑m₂ : Matrix (Fin 2) (Fin 2) C.k) 0 0 ≠ 0 := hm00 ▸ hm00_ne
    exact mul_right_cancel₀ hm₂_ne this
  have hm11 : m₁.val 1 1 = m₂.val 1 1 := by
    have := h_entry 1 1; rw [p₁, p₂] at this
    rw [hu'₁_11, hu₁_11, hu'₂_11, hu₂_11] at this
    simp only [one_mul, mul_one] at this
    rw [hu'10, hm00, hu01] at this
    exact add_left_cancel this
  have h_u'_eq : u'₁ = u'₂ := by
    apply Units.val_injective; ext i j
    fin_cases i <;> fin_cases j <;> first | exact hu'10 | simp_all
  have h_m_eq : m₁ = m₂ := by
    apply Units.val_injective; ext i j
    fin_cases i <;> fin_cases j <;> first | exact hm00 | exact hm11 | simp_all
  have h_u_eq : u₁ = u₂ := by
    apply Units.val_injective; ext i j
    fin_cases i <;> fin_cases j <;> first | exact hu01 | simp_all
  exact Prod.ext h_u'_eq (Prod.ext h_m_eq h_u_eq)



/--
[IwahoriDecomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/IwahoriDecomp.lean)
-/
private lemma IwahoriDecomposition
  {C : DVRContext}
  [DVRClosureGL2 C]
  {C}
  (C) :
-- imply
  ∀ b ∈ C.IwahoriGL2Gen, ∃! (triple : GL (Fin 2) C.k × GL (Fin 2) C.k × GL (Fin 2) C.k), let (u', m, u) := triple u' ∈ C.LowerUnipGL2Gen ∩ C.IwahoriGL2Gen ∧ m ∈ C.DiagGL2Gen ∩ C.IwahoriGL2Gen ∧ u ∈ C.UpperUnipGL2Gen ∩ C.IwahoriGL2Gen ∧ b = u' * m * u := by
-- proof
  rw [iwahoriGL2Gen_eq_iwahoriGL2, lowerUnipGL2Gen_eq_lowerUnipGL2,
    upperUnipGL2Gen_eq_upperUnipGL2, diagGL2Gen_eq_diagGL2]
  intro b hb
  obtain ⟨u', m, u, hu'_mem, hm_mem, hu_mem, heq⟩ :=
    C.iwahori_decomp_gl2_exists b hb
  refine ⟨(u', m, u), ⟨hu'_mem, hm_mem, hu_mem, heq⟩, ?_⟩
  intro ⟨u'₂, m₂, u₂⟩ ⟨hu'₂, hm₂, hu₂, heq₂⟩
  exact C.iwahori_decomp_gl2_unique b hb
    (u'₂, m₂, u₂) (u', m, u)
    ⟨hu'₂, hm₂, hu₂, heq₂⟩ ⟨hu'_mem, hm_mem, hu_mem, heq⟩



/--
[IwahoriDecomposition_concrete](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/IwahoriDecomp.lean)
-/
private lemma IwahoriDecomposition_concrete
  {C : DVRContext}
  [DVRClosureGL2 C]
  {C}
  (C) :
-- imply
  ∀ b ∈ C.IwahoriGL2, ∃! (triple : GL (Fin 2) C.k × GL (Fin 2) C.k × GL (Fin 2) C.k), let (u', m, u) := triple u' ∈ C.LowerUnipGL2 ∩ C.IwahoriGL2 ∧ m ∈ C.DiagGL2 ∩ C.IwahoriGL2 ∧ u ∈ C.UpperUnipGL2 ∩ C.IwahoriGL2 ∧ b = u' * m * u := by
-- proof
  rw [← iwahoriGL2Gen_eq_iwahoriGL2, ← lowerUnipGL2Gen_eq_lowerUnipGL2,
    ← upperUnipGL2Gen_eq_upperUnipGL2, ← diagGL2Gen_eq_diagGL2]
  exact C.IwahoriDecomposition



-- created on 2026-10-23
-- updated on 2026-10-26
