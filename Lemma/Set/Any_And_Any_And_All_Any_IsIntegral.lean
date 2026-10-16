import Mathlib
import sympy.Basic
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Polynomial


private noncomputable def scale
  {K : Type u} [Field K]
  {d : ℕ}
  (u : Fin d → K) :
  MvPolynomial (Fin d) K →ₐ[K] MvPolynomial (Fin d) K :=
  MvPolynomial.aeval fun i => MvPolynomial.C (u i) * MvPolynomial.X i

private lemma exists_mul_eq_of_mem_adjoin
  {R : Type u} {C : Type v} [CommRing R] [IsDomain R] [CommRing C] [Algebra R C]
  {K : Type u} {L : Type v} [Field K] [Field L]
  [Algebra R K] [Algebra C L] [Algebra K L] [Algebra R L]
  [IsScalarTower R C L] [IsScalarTower R K L] [IsFractionRing R K]
  (S : Set C) {w : L}
  (hw : w ∈ Algebra.adjoin K ((algebraMap C L) '' S)) :
  ∃ r : R, r ≠ 0 ∧ ∃ c ∈ Algebra.adjoin R S, algebraMap R L r * w = algebraMap C L c := by
  induction hw using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    exact ⟨1, one_ne_zero, c, Algebra.subset_adjoin hc, by simp⟩
  | algebraMap κ =>
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) κ
    refine ⟨b, nonZeroDivisors.ne_zero hb, algebraMap R C a, Subalgebra.algebraMap_mem _ a, ?_⟩
    have hb' : algebraMap R L b ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply R K L]
      exact (_root_.map_ne_zero _).mpr
        ((_root_.map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr
          (nonZeroDivisors.ne_zero hb))
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, mul_div_cancel₀ _ hb']
  | add x y _ _ ihx ihy =>
    obtain ⟨r, hr, c, hc, e⟩ := ihx
    obtain ⟨r', hr', c', hc', e'⟩ := ihy
    refine ⟨r * r', mul_ne_zero hr hr', r' • c + r • c',
      add_mem (Subalgebra.smul_mem _ hc _) (Subalgebra.smul_mem _ hc' _), ?_⟩
    simp only [map_add, map_mul, Algebra.smul_def, ← IsScalarTower.algebraMap_apply R C L]
    rw [← e, ← e']
    ring
  | mul x y _ _ ihx ihy =>
    obtain ⟨r, hr, c, hc, e⟩ := ihx
    obtain ⟨r', hr', c', hc', e'⟩ := ihy
    refine ⟨r * r', mul_ne_zero hr hr', c * c', mul_mem hc hc', ?_⟩
    rw [map_mul, map_mul, ← e, ← e']
    ring

private lemma scale_comp_scale_inv
  {K : Type u} [Field K]
  {d : ℕ}
  (u : Fin d → K)
  (hu : ∀ i, u i ≠ 0) :
  (scale u).comp (scale fun i => (u i)⁻¹) = AlgHom.id K (MvPolynomial (Fin d) K) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [scale, AlgHom.coe_comp, Function.comp_apply, MvPolynomial.aeval_X, map_mul,
    MvPolynomial.aeval_C, AlgHom.coe_id, id_eq, MvPolynomial.algebraMap_eq]
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (hu i), map_one, one_mul]

private lemma scale_injective
  {K : Type u} [Field K]
  {d : ℕ}
  (u : Fin d → K)
  (hu : ∀ i, u i ≠ 0) :
  Function.Injective (scale u) := by
  have hu' : ∀ i, (u i)⁻¹ ≠ 0 := fun i => inv_ne_zero (hu i)
  have h := scale_comp_scale_inv (fun i => (u i)⁻¹) hu'
  simp only [inv_inv] at h
  intro a b hab
  have := congrArg (scale fun i => (u i)⁻¹) hab
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, h] at this
  simpa using this

private lemma noether_ck_finite_mem
  {R : Type u} {C : Type v} [CommRing R] [IsDomain R] [CommRing C] [IsDomain C]
  [Algebra R C]
  {K : Type u} {L : Type v} [Field K] [Field L]
  [Algebra R K] [Algebra C L] [Algebra K L] [Algebra R L]
  [IsScalarTower R C L] [IsScalarTower R K L]
  [IsFractionRing R K] [IsFractionRing C L]
  (s : Finset C) (hs : Algebra.adjoin R (s : Set C) = ⊤) :
  let CK : Subalgebra K L := Algebra.adjoin K ((algebraMap C L) '' (s : Set C))
  Algebra.FiniteType K CK ∧ ∀ c : C, algebraMap C L c ∈ CK := by
  classical
  let CK : Subalgebra K L := Algebra.adjoin K ((algebraMap C L) '' (s : Set C))
  constructor
  ·
    rw [← Subalgebra.fg_iff_finiteType]
    refine ⟨s.image (algebraMap C L), ?_⟩
    simp [Finset.coe_image]
  ·
    intro c
    have hc : c ∈ Algebra.adjoin R (s : Set C) := hs ▸ Algebra.mem_top
    induction hc using Algebra.adjoin_induction with
    | mem x hx =>
      exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
    | algebraMap r =>
      have hr : algebraMap C L (algebraMap R C r) = algebraMap K L (algebraMap R K r) := by
        rw [← IsScalarTower.algebraMap_apply R C L, ← IsScalarTower.algebraMap_apply R K L]
      rw [hr]
      exact Subalgebra.algebraMap_mem CK (algebraMap R K r)
    | add x y _ _ hx hy =>
      rw [map_add]
      exact add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [map_mul]
      exact mul_mem hx hy

private lemma noether_aeval_of_algHom
  {K : Type u} {L : Type v} [CommRing K] [CommRing L] [Algebra K L]
  {d : ℕ} {CK : Subalgebra K L}
  (g : MvPolynomial (Fin d) K →ₐ[K] CK) :
  ∀ p : MvPolynomial (Fin d) K,
    (g p : L) = MvPolynomial.aeval (fun i => (g (MvPolynomial.X i) : L)) p := by
  intro p
  have : (CK.val.comp g) = MvPolynomial.aeval (fun i => (g (MvPolynomial.X i) : L)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  exact congrArg (fun φ : MvPolynomial (Fin d) K →ₐ[K] L => φ p) this

private lemma noether_algIndep
  {R : Type u} {C : Type v} [CommRing R] [IsDomain R] [CommRing C] [IsDomain C]
  [Algebra R C]
  {K : Type u} {L : Type v} [Field K] [Field L]
  [Algebra R K] [Algebra C L] [Algebra K L] [Algebra R L]
  [IsScalarTower R C L] [IsScalarTower R K L]
  [IsFractionRing R K] [IsFractionRing C L]
  {CK : Subalgebra K L} (d : ℕ) (g : MvPolynomial (Fin d) K →ₐ[K] CK)
  (hginj : Function.Injective g) (ρ : Fin d → R) (z : Fin d → C)
  (hρ0 : ∀ i, ρ i ≠ 0)
  (hz : ∀ i, algebraMap R L (ρ i) * (g (MvPolynomial.X i) : L) = algebraMap C L (z i)) :
  AlgebraicIndependent R z := by
  have hRK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hρK : ∀ i, algebraMap R K (ρ i) ≠ 0 := fun i => (map_ne_zero_iff _ hRK).mpr (hρ0 i)
  have hg_aeval := noether_aeval_of_algHom (L := L) g
  have hzaeval : ∀ p : MvPolynomial (Fin d) K,
      MvPolynomial.aeval (fun i => algebraMap C L (z i)) p =
        (g (scale (fun i => algebraMap R K (ρ i)) p) : L) := by
    intro p
    rw [hg_aeval]
    have : (MvPolynomial.aeval (fun i => algebraMap C L (z i)) : MvPolynomial (Fin d) K →ₐ[K] L) =
      (MvPolynomial.aeval (fun i => (g (MvPolynomial.X i) : L))).comp
        (scale fun i => algebraMap R K (ρ i)) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [MvPolynomial.aeval_X, AlgHom.coe_comp, Function.comp_apply, scale, map_mul,
        MvPolynomial.aeval_C]
      rw [← hz i, IsScalarTower.algebraMap_apply R K L]
    exact congrArg (fun φ : MvPolynomial (Fin d) K →ₐ[K] L => φ p) this
  rw [AlgebraicIndependent]
  intro p q hpq
  have h1 : MvPolynomial.aeval (fun i => algebraMap C L (z i))
      (MvPolynomial.map (algebraMap R K) p) =
      MvPolynomial.aeval (fun i => algebraMap C L (z i))
        (MvPolynomial.map (algebraMap R K) q) := by
    rw [MvPolynomial.aeval_map_algebraMap, MvPolynomial.aeval_map_algebraMap]
    have e : ∀ t : MvPolynomial (Fin d) R,
        MvPolynomial.aeval (fun i => algebraMap C L (z i)) t =
          algebraMap C L (MvPolynomial.aeval z t) := by
      intro t
      rw [← MvPolynomial.aeval_algebraMap_apply]
      rfl
    rw [e, e]
    exact congrArg _ hpq
  rw [hzaeval, hzaeval] at h1
  have h2 := hginj (Subtype.ext h1)
  have h3 := scale_injective _ hρK h2
  refine MvPolynomial.map_injective _ hRK h3

private lemma noether_g_mem_adjoin_z
  {R : Type u} {C : Type v} [CommRing R] [IsDomain R] [CommRing C] [IsDomain C]
  [Algebra R C]
  {K : Type u} {L : Type v} [Field K] [Field L]
  [Algebra R K] [Algebra C L] [Algebra K L] [Algebra R L]
  [IsScalarTower R C L] [IsScalarTower R K L]
  {CK : Subalgebra K L} (d : ℕ) (g : MvPolynomial (Fin d) K →ₐ[K] CK)
  (ρ : Fin d → R) (z : Fin d → C)
  (hρK : ∀ i, algebraMap R K (ρ i) ≠ 0)
  (hz : ∀ i, algebraMap R L (ρ i) * (g (MvPolynomial.X i) : L) = algebraMap C L (z i)) :
  ∀ p : MvPolynomial (Fin d) K,
    (g p : L) ∈ Algebra.adjoin K ((algebraMap C L) '' Set.range z) := by
  intro p
  have hg_aeval := noether_aeval_of_algHom (L := L) g
  rw [hg_aeval]
  induction p using MvPolynomial.induction_on with
  | C κ =>
    rw [MvPolynomial.aeval_C]
    apply Subalgebra.algebraMap_mem _ κ
  | add p q hp hq =>
    rw [map_add]
    apply add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul, MvPolynomial.aeval_X]
    refine mul_mem hp ?_
    have : (g (MvPolynomial.X i) : L) =
        algebraMap K L (algebraMap R K (ρ i))⁻¹ * algebraMap C L (z i) := by
      rw [← hz i, IsScalarTower.algebraMap_apply R K L, ← mul_assoc, ← map_mul,
        inv_mul_cancel₀ (hρK i), map_one, one_mul]
    rw [this]
    apply mul_mem (Subalgebra.algebraMap_mem _ _)
      (Algebra.subset_adjoin (Set.mem_image_of_mem (algebraMap C L) (Set.mem_range_self i)))

private lemma noether_integral_clear
  {R : Type u} {C : Type v} [CommRing R] [IsDomain R] [CommRing C] [IsDomain C]
  [Algebra R C]
  {K : Type u} {L : Type v} [Field K] [Field L]
  [Algebra R K] [Algebra C L] [Algebra K L] [Algebra R L]
  [IsScalarTower R C L] [IsScalarTower R K L]
  [IsFractionRing R K] [IsFractionRing C L]
  {CK : Subalgebra K L} (d : ℕ) (g : MvPolynomial (Fin d) K →ₐ[K] CK)
  (hgfin : g.Finite) (ρ : Fin d → R) (z : Fin d → C)
  (hmemCK : ∀ c : C, algebraMap C L c ∈ CK)
  (hρK : ∀ i, algebraMap R K (ρ i) ≠ 0)
  (hz : ∀ i, algebraMap R L (ρ i) * (g (MvPolynomial.X i) : L) = algebraMap C L (z i))
  (c : C) :
  ∃ τ : R, τ ≠ 0 ∧ IsIntegral (Algebra.adjoin R (Set.range z)) (τ • c) := by
  have hCL : Function.Injective (algebraMap C L) := IsFractionRing.injective C L
  set A : Subalgebra R C := Algebra.adjoin R (Set.range z)
  have hrange := noether_g_mem_adjoin_z (R := R) (C := C) (K := K) (L := L) (CK := CK)
    d g ρ z hρK hz
  have hgint : g.toRingHom.IsIntegral := RingHom.Finite.to_isIntegral hgfin
  obtain ⟨P, hPm, hP⟩ := hgint ⟨algebraMap C L c, hmemCK c⟩
  let P₂ : L[X] := (P.map g.toRingHom).map (CK.val : CK →+* L)
  have hP₂m : P₂.Monic := (hPm.map _).map _
  have hP₂ : P₂.eval (algebraMap C L c) = 0 := by
    have h2 : (CK.val : CK →+* L) (P.eval₂ g.toRingHom ⟨_, hmemCK c⟩) = 0 := by
      rw [hP, map_zero]
    rw [Polynomial.hom_eval₂] at h2
    simp only [P₂, Polynomial.map_map, Polynomial.eval_map]
    exact h2
  have hcoef : ∀ j : ℕ, ∃ r : R, r ≠ 0 ∧ ∃ a ∈ A, algebraMap R L r * P₂.coeff j =
      algebraMap C L a := by
    intro j
    have hj : P₂.coeff j ∈ Algebra.adjoin K ((algebraMap C L) '' Set.range z) := by
      simp only [P₂, Polynomial.coeff_map]
      apply hrange _
    refine exists_mul_eq_of_mem_adjoin (R := R) (K := K) (L := L) (S := Set.range z) hj
  choose r hr0 a haA ha using hcoef
  let τ : R := ∏ j ∈ Finset.range P₂.natDegree, r j
  have hτ0 : τ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hr0 j
  refine ⟨τ, hτ0, ?_⟩
  let P₃ : L[X] := P₂.scaleRoots (algebraMap R L τ)
  have hP₃m : P₃.Monic := (Polynomial.monic_scaleRoots_iff _).mpr hP₂m
  have hP₃ : P₃.eval₂ (RingHom.id L) (algebraMap R L τ * algebraMap C L c) = 0 := by
    have h := Polynomial.scaleRoots_eval₂_eq_zero (RingHom.id L) (r := algebraMap C L c)
      (s := algebraMap R L τ) (by rwa [Polynomial.eval₂_id])
    simpa using h
  have hlift : P₃ ∈ Polynomial.lifts (algebraMap A L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro j
    simp only [P₃, Polynomial.coeff_scaleRoots]
    if hj : j < P₂.natDegree then
      obtain ⟨k, hk⟩ : ∃ k, P₂.natDegree - j = k + 1 := ⟨P₂.natDegree - j - 1, by omega⟩
      have hdvd : r j ∣ τ := Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hj)
      obtain ⟨τ', hτ'⟩ := hdvd
      refine ⟨⟨algebraMap R C (τ' * τ ^ k) * a j,
        mul_mem (Subalgebra.algebraMap_mem _ _) (haA j)⟩, ?_⟩
      change algebraMap C L (algebraMap R C (τ' * τ ^ k) * a j) =
        P₂.coeff j * algebraMap R L τ ^ (P₂.natDegree - j)
      rw [hk, map_mul, ← IsScalarTower.algebraMap_apply, ← ha j, pow_succ, hτ', map_mul,
        map_mul, map_pow, map_mul]
      ring
    else if hj' : j = P₂.natDegree then
      subst hj'
      refine ⟨1, ?_⟩
      rw [hP₂m.coeff_natDegree, Nat.sub_self, pow_zero, one_mul, map_one]
    else
      refine ⟨0, ?_⟩
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul, map_zero]
  obtain ⟨Q, hQmap, -, hQm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hP₃m
  have hτc : IsIntegral A (algebraMap C L (τ • c)) := by
    refine ⟨Q, hQm, ?_⟩
    rwa [Polynomial.eval₂_eq_eval_map, hQmap, Polynomial.eval, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply]
  refine (isIntegral_algHom_iff (IsScalarTower.toAlgHom A C L) hCL).mp hτc

private lemma noether_pow_smul_of_gens
  {R : Type u} {C : Type v} [CommRing R] [IsDomain R] [CommRing C] [Algebra R C]
  (A : Subalgebra R C) (s : Finset C) (τ : C → R) (r : R)
  (hr : ∀ c ∈ s, τ c ∣ r)
  (hτint : ∀ c ∈ s, IsIntegral A (τ c • c))
  (hs : Algebra.adjoin R (s : Set C) = ⊤) :
  ∀ c : C, ∃ n : ℕ, IsIntegral A (r ^ n • c) := by
  have hAint : ∀ x : R, IsIntegral A (algebraMap R C x) := fun x =>
    isIntegral_algebraMap (R := A) (A := C)
      (x := ⟨algebraMap R C x, Subalgebra.algebraMap_mem _ x⟩)
  let T : Subalgebra R C :=
    { carrier := {c | ∃ n : ℕ, IsIntegral A (r ^ n • c)}
      mul_mem' := by
        rintro a b ⟨n, ha⟩ ⟨m, hb⟩
        refine ⟨n + m, ?_⟩
        have : r ^ (n + m) • (a * b) = (r ^ n • a) * (r ^ m • b) := by
          rw [pow_add, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul]
          ring
        rw [this]
        exact ha.mul hb
      add_mem' := by
        rintro a b ⟨n, ha⟩ ⟨m, hb⟩
        refine ⟨n + m, ?_⟩
        have : r ^ (n + m) • (a + b) =
            algebraMap R C (r ^ m) * (r ^ n • a) + algebraMap R C (r ^ n) * (r ^ m • b) := by
          rw [pow_add, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul]
          ring
        rw [this]
        exact ((hAint _).mul ha).add ((hAint _).mul hb)
      algebraMap_mem' := by
        intro x
        refine ⟨0, ?_⟩
        rw [pow_zero, one_smul]
        exact hAint x }
  have hsT : (s : Set C) ⊆ T := by
    intro c hc
    refine ⟨1, ?_⟩
    obtain ⟨r', hr'⟩ := hr c hc
    have : r ^ 1 • c = algebraMap R C r' * (τ c • c) := by
      rw [pow_one, hr', Algebra.smul_def, Algebra.smul_def, map_mul]
      ring
    rw [this]
    exact (hAint r').mul (hτint c hc)
  have hT : Algebra.adjoin R (s : Set C) ≤ T := Algebra.adjoin_le hsT
  intro c
  exact hT (hs ▸ Algebra.mem_top)

private lemma noether_exists_finite_inj
  {K : Type u} {L : Type v} [Field K] [CommRing L] [Nontrivial L] [Algebra K L]
  {CK : Subalgebra K L} [Algebra.FiniteType K CK] :
  ∃ d, ∃ g : MvPolynomial (Fin d) K →ₐ[K] CK, Function.Injective g ∧ g.Finite :=
  exists_finite_inj_algHom_of_fg K CK

set_option backward.isDefEq.respectTransparency false in
private lemma noether_main
  {R : Type u} {C : Type v} [CommRing R] [IsDomain R] [CommRing C] [IsDomain C]
  [Algebra R C] [FaithfulSMul R C] [Algebra.FiniteType R C] :
  ∃ r : R, r ≠ 0 ∧ ∃ (d : ℕ) (z : Fin d → C), AlgebraicIndependent R z ∧
    ∀ c : C, ∃ n : ℕ, IsIntegral (Algebra.adjoin R (Set.range z)) (r ^ n • c) := by
  classical
  let K := FractionRing R
  let L := FractionRing C
  let : Algebra K L := FractionRing.liftAlgebra R L
  have : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := C)
  let CK : Subalgebra K L := Algebra.adjoin K ((algebraMap C L) '' (s : Set C))
  have hfin_mem := noether_ck_finite_mem (R := R) (C := C) (K := K) (L := L) s hs
  have : Algebra.FiniteType K CK := hfin_mem.1
  have hmemCK : ∀ c : C, algebraMap C L c ∈ CK := hfin_mem.2
  obtain ⟨d, g, hginj, hgfin⟩ := noether_exists_finite_inj (K := K) (L := L) (CK := CK)
  have hw : ∀ i : Fin d, ∃ r : R, r ≠ 0 ∧ ∃ c ∈ Algebra.adjoin R (s : Set C),
      algebraMap R L r * (g (MvPolynomial.X i) : L) = algebraMap C L c :=
    fun i => exists_mul_eq_of_mem_adjoin (R := R) _ (g (MvPolynomial.X i)).2
  choose ρ hρ0 z hzmem hz using hw
  have hRK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hρK : ∀ i, algebraMap R K (ρ i) ≠ 0 := fun i => (map_ne_zero_iff _ hRK).mpr (hρ0 i)
  have hzind : AlgebraicIndependent R z :=
    noether_algIndep (R := R) (C := C) (K := K) (L := L) (CK := CK) d g hginj ρ z hρ0 hz
  set A : Subalgebra R C := Algebra.adjoin R (Set.range z)
  have hint : ∀ c : C, ∃ τ : R, τ ≠ 0 ∧ IsIntegral A (τ • c) := fun c =>
    noether_integral_clear (R := R) (C := C) (K := K) (L := L) (CK := CK)
      d g hgfin ρ z hmemCK hρK hz c
  choose τ hτ0 hτint using hint
  let r : R := ∏ c ∈ s, τ c
  have hr0 : r ≠ 0 := Finset.prod_ne_zero_iff.mpr fun c _ => hτ0 c
  refine ⟨r, hr0, d, z, hzind, ?_⟩
  exact noether_pow_smul_of_gens A s τ r
    (fun c hc => Finset.dvd_prod_of_mem _ hc)
    (fun c _ => hτint c) hs


/--
[Algebra_exists_ne_zero_algebraicIndependent_forall_isIntegral_pow_smul_of_finiteType](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_exists_ne_zero_algebraicIndependent_forall_isIntegral_pow_smul_of_finiteType.lean)
-/
@[path]
private lemma main
  {R : Type u} {C : Type v} [CommRing R] [IsDomain R] [CommRing C] [IsDomain C]
  [Algebra R C] [FaithfulSMul R C] [Algebra.FiniteType R C] :
  ∃ r : R, r ≠ 0 ∧ ∃ (d : ℕ) (z : Fin d → C), AlgebraicIndependent R z ∧
    ∀ c : C, ∃ n : ℕ, IsIntegral (Algebra.adjoin R (Set.range z)) (r ^ n • c) := by
  apply noether_main


-- created on 2026-10-16
