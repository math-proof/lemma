import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v w

private abbrev v2 {α : Type*} (a b : α) : Fin 2 → α :=
  Matrix.vecCons a (Matrix.vecCons b Matrix.vecEmpty)

private abbrev m2 {α : Type*} (a b c d : α) : Matrix (Fin 2) (Fin 2) α :=
  Matrix.of (Matrix.vecCons (v2 a b) (Matrix.vecCons (v2 c d) Matrix.vecEmpty))

private noncomputable def E {A : Type u} [Ring A] (p : Bool × A) : Matrix (Fin 2) (Fin 2) A :=
  if p.1 then m2 (1 : A) p.2 0 1 else m2 (1 : A) 0 p.2 1

private noncomputable def W {A : Type u} [Ring A] (l : List (Bool × A)) : Matrix (Fin 2) (Fin 2) A :=
  (l.map E).prod

private lemma W_def {A : Type u} [Ring A] (l : List (Bool × A)) : W l = (l.map fun p : Bool × A => if p.1 then m2 (1 : A) p.2 0 1 else m2 (1 : A) 0 p.2 1).prod := rfl

@[simp] private lemma W_nil {A : Type u} [Ring A] : W ([] : List (Bool × A)) = 1 := by
  simp [W]

@[simp] private lemma W_cons {A : Type u} [Ring A] (p : Bool × A) (l : List (Bool × A)) : W (p :: l) = E p * W l := by
  simp [W]

private lemma W_append {A : Type u} [Ring A] (l l' : List (Bool × A)) : W (l ++ l') = W l * W l' := by
  simp [W, List.map_append, List.prod_append]

@[simp] private lemma E_true {A : Type u} [Ring A] (t : A) : E (true, t) = m2 (1 : A) t 0 1 := rfl

@[simp] private lemma E_false {A : Type u} [Ring A] (t : A) : E (false, t) = m2 (1 : A) 0 t 1 := rfl

private lemma fin_two_eq {A : Type u} {a b c d a' b' c' d' : A} (h₁ : a = a') (h₂ : b = b') (h₃ : c = c') (h₄ : d = d') : m2 a b c d = m2 a' b' c' d' := by
  subst h₁ h₂ h₃ h₄
  rfl

private lemma upper_mul {A : Type u} [Ring A] (t a b c d : A) : m2 (1 : A) t 0 1 * m2 a b c d = m2 (a + t * c) (b + t * d) c d := by
  rw [Matrix.mul_fin_two]
  refine fin_two_eq (by noncomm_ring) (by noncomm_ring) (by noncomm_ring) (by noncomm_ring)

private lemma lower_mul {A : Type u} [Ring A] (t a b c d : A) : m2 (1 : A) 0 t 1 * m2 a b c d = m2 a b (t * a + c) (t * b + d) := by
  rw [Matrix.mul_fin_two]
  refine fin_two_eq (by noncomm_ring) (by noncomm_ring) (by noncomm_ring) (by noncomm_ring)

private lemma one_eq {A : Type u} [Ring A] : (1 : Matrix (Fin 2) (Fin 2) A) = m2 (1 : A) 0 0 1 := Matrix.one_fin_two

private lemma diag_mul_diag {A : Type u} [Ring A] (x y : A) : m2 (1 : A) 0 0 x * m2 (1 : A) 0 0 y = m2 (1 : A) 0 0 (x * y) := by
  rw [Matrix.mul_fin_two]
  refine fin_two_eq (by noncomm_ring) (by noncomm_ring) (by noncomm_ring) (by noncomm_ring)

private lemma W_commutator {A : Type u} [Ring A] (P Q : A) (h : Q * P = 0) : W [(false, P), (true, Q), (false, -P), (true, -Q)] = m2 (1 : A) 0 0 (1 + P * Q) := by
  have hx : ∀ x : A, Q * (P * x) = 0 := fun x => by rw [← mul_assoc, h, zero_mul]
  simp only [W_cons, W_nil, E_true, E_false, one_eq, upper_mul, lower_mul]
  refine fin_two_eq ?_ ?_ ?_ ?_
  · simp [mul_add, add_mul, mul_assoc, h, hx]
  · simp [mul_add, add_mul, mul_assoc, h, hx]
  · simp [mul_add, add_mul, mul_assoc, h, hx]
  · simp [mul_add, add_mul, mul_assoc, h, hx]

private lemma W_weyl {A : Type u} [Ring A] : W [(true, (1 : A)), (false, -1), (true, 1)] = m2 (0 : A) 1 (-1) 0 := by
  simp only [W_cons, W_nil, E_true, E_false, one_eq, upper_mul, lower_mul]
  refine fin_two_eq (by noncomm_ring) (by noncomm_ring) (by noncomm_ring) (by noncomm_ring)

private lemma W_weyl_inv {A : Type u} [Ring A] : W [(true, (-1 : A)), (false, 1), (true, -1)] = m2 (0 : A) (-1) 1 0 := by
  simp only [W_cons, W_nil, E_true, E_false, one_eq, upper_mul, lower_mul]
  refine fin_two_eq (by noncomm_ring) (by noncomm_ring) (by noncomm_ring) (by noncomm_ring)

private lemma W_conj_diag {A : Type u} [Ring A] (l : List (Bool × A)) (s : A) (hl : W l = m2 (1 : A) 0 0 s) : W ([(true, (1 : A)), (false, -1), (true, 1)] ++ l ++ [(true, (-1 : A)), (false, 1), (true, -1)]) = m2 s 0 0 1 := by
  rw [W_append, W_append, W_weyl, hl, W_weyl_inv, Matrix.mul_fin_two, Matrix.mul_fin_two]
  refine fin_two_eq (by noncomm_ring) (by noncomm_ring) (by noncomm_ring) (by noncomm_ring)

private lemma W_diag_mul {A : Type u} [Ring A] {l l' : List (Bool × A)} {x y : A} (hl : W l = m2 (1 : A) 0 0 x) (hl' : W l' = m2 (1 : A) 0 0 y) : W (l ++ l') = m2 (1 : A) 0 0 (x * y) := by
  rw [W_append, hl, hl', diag_mul_diag]

private lemma W_whitehead {A : Type u} [Ring A] (u : Units A) : W [(true, ((u⁻¹ : Units A) : A)), (false, -(u : A)), (true, ((u⁻¹ : Units A) : A)), (true, (-1 : A)), (false, 1), (true, -1)] = m2 ((u⁻¹ : Units A) : A) 0 0 (u : A) := by
  simp only [W_cons, W_nil, E_true, E_false, one_eq, upper_mul, lower_mul]
  refine fin_two_eq ?_ ?_ ?_ ?_
  · simp [mul_add, add_mul, mul_assoc]
  · simp [mul_add, add_mul, mul_assoc]
  · simp [mul_add, add_mul, mul_assoc]
  · simp [mul_add, add_mul, mul_assoc]

private lemma diag_units_eq {A : Type u} [Ring A] (g₁ g₂ : Units A) : (m2 (g₁ : A) 0 0 (g₂ : A) : Matrix (Fin 2) (Fin 2) A) = m2 ((g₁ : A) * g₂) 0 0 1 * m2 ((g₂⁻¹ : Units A) : A) 0 0 (g₂ : A) := by
  rw [Matrix.mul_fin_two]
  refine fin_two_eq ?_ ?_ ?_ ?_
  · simp [mul_assoc]
  · simp [mul_assoc]
  · simp [mul_assoc]
  · simp [mul_assoc]

private lemma map_W {A : Type u} [Ring A] {B : Type w} [Ring B] (f : A →+* B) (l : List (Bool × A)) : f.mapMatrix (W l) = W (l.map fun p => (p.1, f p.2)) := by
  induction l
  · simp [W]
  ·
    rename_i p l ih
    rw [W_cons, map_mul, ih, List.map_cons, W_cons]
    congr 1
    obtain ⟨b, t⟩ := p
    cases b
    ·
      simp only [E_false]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    ·
      simp only [E_true]
      ext i j
      fin_cases i <;> fin_cases j <;> simp

private lemma exists_W_eq_diag_upper {F : Type v} [Field F] (t : F) : ∃ l : List (Bool × Matrix (Fin 2) (Fin 2) F), W l = m2 (1 : Matrix (Fin 2) (Fin 2) F) 0 0 (m2 (1 : F) t 0 1) := by
  refine ⟨[(false, m2 t 0 0 0), (true, m2 0 1 0 0), (false, -(m2 t 0 0 0)), (true, -(m2 0 1 0 0))], ?_⟩
  rw [W_commutator]
  ·
    refine fin_two_eq rfl rfl rfl ?_
    rw [one_eq, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  ·
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

private lemma exists_W_eq_diag_lower {F : Type v} [Field F] (t : F) : ∃ l : List (Bool × Matrix (Fin 2) (Fin 2) F), W l = m2 (1 : Matrix (Fin 2) (Fin 2) F) 0 0 (m2 (1 : F) 0 t 1) := by
  refine ⟨[(false, m2 0 0 t 0), (true, m2 1 0 0 0), (false, -(m2 0 0 t 0)), (true, -(m2 1 0 0 0))], ?_⟩
  rw [W_commutator]
  ·
    refine fin_two_eq rfl rfl rfl ?_
    rw [one_eq, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  ·
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

private lemma exists_eq_prod_of_det_eq_one' {F : Type v} [Field F] (a b c d : F) (h : a * d - b * c = 1) : ∃ e x y z : F, (m2 a b c d : Matrix (Fin 2) (Fin 2) F) = m2 (1 : F) 0 (-e) 1 * m2 (1 : F) x 0 1 * m2 (1 : F) 0 y 1 * m2 (1 : F) z 0 1 := by
  if hc : c = 0 then
    subst hc
    have had : a * d = 1 := by
      rwa [mul_zero, sub_zero] at h
    have : a ≠ 0 := left_ne_zero_of_mul_eq_one had
    refine ⟨1, (a - 1) / a, a, (b + d - 1) / a, ?_⟩
    simp only [Matrix.mul_fin_two]
    refine fin_two_eq ?_ ?_ ?_ ?_
    ·
      field_simp
      ring
    ·
      field_simp
      linear_combination -had
    ·
      field_simp
      ring
    ·
      field_simp
      linear_combination had
  else
    refine ⟨0, (a - 1) / c, c, (d - 1) / c, ?_⟩
    simp only [Matrix.mul_fin_two]
    refine fin_two_eq ?_ ?_ ?_ ?_
    ·
      field_simp
      ring
    ·
      field_simp
      linear_combination -h
    · simp
    ·
      field_simp
      ring

private lemma exists_eq_prod_of_det_eq_one {F : Type v} [Field F] (s : Matrix (Fin 2) (Fin 2) F) (hs : s.det = 1) : ∃ e x y z : F, s = m2 (1 : F) 0 (-e) 1 * m2 (1 : F) x 0 1 * m2 (1 : F) 0 y 1 * m2 (1 : F) z 0 1 := by
  rw [Matrix.det_fin_two] at hs
  rw [Matrix.eta_fin_two s]
  refine exists_eq_prod_of_det_eq_one' _ _ _ _ hs

private lemma exists_W_eq_diag_of_det_eq_one {F : Type v} [Field F] (s : Matrix (Fin 2) (Fin 2) F) (hs : s.det = 1) : ∃ l : List (Bool × Matrix (Fin 2) (Fin 2) F), W l = m2 (1 : Matrix (Fin 2) (Fin 2) F) 0 0 s := by
  obtain ⟨e, x, y, z, rfl⟩ := exists_eq_prod_of_det_eq_one s hs
  obtain ⟨l₁, h₁⟩ := exists_W_eq_diag_lower (F := F) (-e)
  obtain ⟨l₂, h₂⟩ := exists_W_eq_diag_upper (F := F) x
  obtain ⟨l₃, h₃⟩ := exists_W_eq_diag_lower (F := F) y
  obtain ⟨l₄, h₄⟩ := exists_W_eq_diag_upper (F := F) z
  refine ⟨_, W_diag_mul (W_diag_mul (W_diag_mul h₁ h₂) h₃) h₄⟩

private lemma exists_W_eq_diag {A : Type u} [Ring A] {F : Type v} [Field F] (φ : A ≃+* Matrix (Fin 2) (Fin 2) F) (s : A) (hs : (φ s).det = 1) : ∃ l : List (Bool × A), W l = m2 (1 : A) 0 0 s := by
  obtain ⟨l, hl⟩ := exists_W_eq_diag_of_det_eq_one (φ s) hs
  refine ⟨l.map fun p => (p.1, φ.symm p.2), ?_⟩
  have := map_W (φ.symm : Matrix (Fin 2) (Fin 2) F →+* A) l
  simp only [RingHom.coe_coe] at this
  rw [← this, hl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/--
[Matrix_exists_list_prod_elementary_eq_diagonal_of_det_map_mul_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Matrix_exists_list_prod_elementary_eq_diagonal_of_det_map_mul_eq_one.lean)
-/
@[path]
private lemma main
  {A : Type u} [Ring A]
  {F : Type v} [Field F]
  (φ : A ≃+* Matrix (Fin 2) (Fin 2) F)
  (g₁ g₂ : Units A)
  -- given
  (h : (φ ((g₁ : A) * g₂)).det = 1) :
  -- imply
  ∃ l : List (Bool × A),
    (l.map fun p : Bool × A =>
      if p.1 then m2 (1 : A) p.2 0 1 else m2 (1 : A) 0 p.2 1).prod = m2 (g₁ : A) 0 0 (g₂ : A) := by
  -- proof
  obtain ⟨l, hl⟩ := exists_W_eq_diag φ ((g₁ : A) * g₂) h
  refine ⟨([(true, (1 : A)), (false, -1), (true, 1)] ++ l ++ [(true, (-1 : A)), (false, 1), (true, -1)]) ++
      [(true, ((g₂⁻¹ : Units A) : A)), (false, -(g₂ : A)), (true, ((g₂⁻¹ : Units A) : A)),
        (true, (-1 : A)), (false, 1), (true, -1)], ?_⟩
  rw [diag_units_eq g₁ g₂]
  change W _ = _
  rw [W_append, W_conj_diag l _ hl, W_whitehead]


-- created on 2026-10-20
