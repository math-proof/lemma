import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false


variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {n : Type} [Fintype n] [DecidableEq n]
private noncomputable def colMat (j₀ : n) (c : n → K) : Matrix n n K :=
  Matrix.of fun i k => if k = j₀ then c i else 0
@[simp] private lemma colMat_apply (j₀ : n) (c : n → K) (i k : n) : colMat j₀ c i k = if k = j₀ then c i else 0 := rfl
private lemma colMat_add (j₀ : n) (c c' : n → K) : colMat j₀ (c + c') = colMat j₀ c + colMat j₀ c' := by
  ext i k
  simp only [colMat_apply, Pi.add_apply, Matrix.add_apply]
  split_ifs
  · simp
  · simp
private lemma colMat_zero (j₀ : n) : colMat j₀ (0 : n → K) = 0 := by
  ext i k
  simp
private lemma colMat_smul (j₀ : n) (a : K) (c : n → K) : colMat j₀ (a • c) = a • colMat j₀ c := by
  ext i k
  simp only [colMat_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
  split_ifs
  · simp
  · simp
private lemma colMat_mul (j₀ : n) (c : n → K) (M : Matrix n n K) : colMat j₀ c * M = Matrix.of fun i k => c i * M j₀ k := by
  ext i k
  rw [Matrix.mul_apply, Matrix.of_apply, Finset.sum_eq_single j₀]
  · simp
  ·
    intro l _ hl
    simp [hl]
  ·
    intro h
    exact absurd (Finset.mem_univ j₀) h
private lemma map_single_one (j j' : n) : (Matrix.single j j' (1 : R)).map (algebraMap R K) = Matrix.single j j' (1 : K) := by
  ext i k
  simp only [Matrix.map_apply, Matrix.single_apply]
  split_ifs
  · simp
  · simp
private lemma mul_single_one (x : Matrix n n K) (j j' : n) : x * Matrix.single j j' (1 : K) = Matrix.of fun i k => if k = j' then x i j else 0 := by
  ext i k
  rw [Matrix.mul_apply, Matrix.of_apply, Finset.sum_eq_single j]
  ·
    rw [Matrix.single_apply]
    if h : k = j' then
      rw [ite_eq_left ⟨rfl, h.symm⟩, ite_eq_left h, mul_one]
    else
      rw [ite_eq_right (fun h' => h h'.2.symm), ite_eq_right h, mul_zero]
  ·
    intro l _ hl
    rw [Matrix.single_apply, ite_eq_right (fun h => hl h.1.symm), mul_zero]
  ·
    intro h
    exact absurd (Finset.mem_univ j) h
private lemma colMat_col_eq_mul (j₀ : n) (x : Matrix n n K) (j : n) : colMat j₀ (fun i => x i j) = x * Matrix.single j j₀ (1 : K) := by
  rw [mul_single_one]
  rfl
private lemma sum_colMat_mul_single (j₀ : n) (x : Matrix n n K) : ∑ j, colMat j₀ (fun i => x i j) * Matrix.single j₀ j (1 : K) = x := by
  ext i k
  rw [Matrix.sum_apply]
  simp only [colMat_mul, Matrix.of_apply, Matrix.single_apply, true_and, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single k]
  · simp
  ·
    intro l _ hl
    rw [ite_eq_right hl]
  ·
    intro h
    exact absurd (Finset.mem_univ k) h
/--
[Matrix_exists_generalLinearGroup_forall_mem_addSubgroup_iff_of_isPrincipalIdealRing](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Matrix_exists_generalLinearGroup_forall_mem_addSubgroup_iff_of_isPrincipalIdealRing.lean)
-/
@[path]
private lemma main
  {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
  {n : Type} [Fintype n] [DecidableEq n]
  (L : AddSubgroup (Matrix n n K))
  -- given
  (hmul : ∀ x ∈ L, ∀ m : Matrix n n R, x * m.map (algebraMap R K) ∈ L)
  (hbdd : ∃ d : R, d ≠ 0 ∧ ∀ x ∈ L, ∀ i j, algebraMap R K d * x i j ∈ (algebraMap R K).range)
  (hfull : ∃ N : R, N ≠ 0 ∧ ∀ m : Matrix n n R, algebraMap R K N • m.map (algebraMap R K) ∈ L) :
  -- imply
  ∃ g : GL n K, ∀ x : Matrix n n K, x ∈ L ↔ ∀ i j, (((g⁻¹ : GL n K) : Matrix n n K) * x) i j ∈ (algebraMap R K).range := by
  -- proof
  classical
  set A := algebraMap R K with hAdef
  have hA : Function.Injective A := IsFractionRing.injective R K
  obtain hn | ⟨⟨j₀⟩⟩ := isEmpty_or_nonempty n
  ·
    refine ⟨1, fun x => ?_⟩
    have hx : x = 0 := Subsingleton.elim _ _
    constructor
    ·
      intro _ i
      exact isEmptyElim i
    ·
      intro _
      rw [hx]
      refine L.zero_mem
  have hunit : ∀ x ∈ L, ∀ j j' : n, x * Matrix.single j j' (1 : K) ∈ L := by
    intro x hx j j'
    have := hmul x hx (Matrix.single j j' 1)
    rwa [map_single_one] at this
  let C : Submodule R (n → K) :=
    { carrier := {c | colMat j₀ c ∈ L}
      add_mem' := fun {c c'} hc hc' => by
        show colMat j₀ (c + c') ∈ L
        rw [colMat_add]
        refine L.add_mem hc hc'
      zero_mem' := by
        show colMat j₀ 0 ∈ L
        rw [colMat_zero]
        refine L.zero_mem
      smul_mem' := fun r c hc => by
        show colMat j₀ (r • c) ∈ L
        rw [← algebraMap_smul K r c, colMat_smul]
        have h := hmul _ hc (Matrix.single j₀ j₀ r)
        have e : (Matrix.single j₀ j₀ r).map (algebraMap R K) = algebraMap R K r • Matrix.single j₀ j₀ (1 : K) := by
          ext i k
          simp only [Matrix.map_apply, Matrix.single_apply, Matrix.smul_apply, smul_eq_mul, mul_ite, mul_one,
            mul_zero]
          split_ifs
          · simp
          · simp
        rw [e, Matrix.mul_smul, ← colMat_col_eq_mul] at h
        have hcc : (fun i => colMat j₀ c i j₀) = c := funext fun i => by simp
        rw [hcc] at h
        refine h }
  have hCmem : ∀ {c : n → K}, c ∈ C ↔ colMat j₀ c ∈ L := fun {c} => Iff.rfl
  have hcol : ∀ x : Matrix n n K, x ∈ L ↔ ∀ j, (fun i => x i j) ∈ C := by
    intro x
    constructor
    ·
      intro hx j
      rw [hCmem, colMat_col_eq_mul]
      refine hunit x hx j j₀
    ·
      intro h
      rw [← sum_colMat_mul_single j₀ x]
      refine L.sum_mem fun j _ => hunit _ (h j) j₀ j
  obtain ⟨d, hd0, hd⟩ := hbdd
  have hAd : A d ≠ 0 := (map_ne_zero_iff A hA).mpr hd0
  let M₀ : Submodule R (n → K) := Submodule.span R (Set.range fun i : n => (A d)⁻¹ • (Pi.single i (1 : K) : n → K))
  have hCM₀ : C ≤ M₀ := by
    intro c hc
    have hint : ∀ i, ∃ r : R, A r = A d * c i := by
      intro i
      obtain ⟨r, hr⟩ := hd _ hc i j₀
      have hr' := hr
      simp at hr'
      exact ⟨r, hr'⟩
    choose r hr using hint
    have hmem : ∀ i, (Pi.single i (c i) : n → K) ∈ M₀ := by
      intro i
      have e1 : (Pi.single i (c i) : n → K) = r i • ((A d)⁻¹ • (Pi.single i (1 : K) : n → K)) := by
        rw [← algebraMap_smul K (r i), smul_smul, hr i]
        ext k
        simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
        split_ifs with hk
        · field_simp
        · rfl
      rw [e1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    rw [← Finset.univ_sum_single c]
    exact Submodule.sum_mem _ fun i _ => hmem i
  have hfg : M₀.FG := Submodule.fg_span (Set.finite_range _)
  let _ : Module.Finite R M₀ := Module.Finite.iff_fg.mpr hfg
  let _ : IsNoetherian R M₀ := isNoetherian_of_isNoetherianRing_of_finite R M₀
  let _ : Module.Finite R C :=
    Module.Finite.of_injective (Submodule.inclusion hCM₀) (Submodule.inclusion_injective hCM₀)
  let _ : Module.IsTorsionFree R C :=
    Subtype.val_injective.moduleIsTorsionFree (Subtype.val : C → n → K) (fun _ _ => rfl)
  let _ : Module.Free R C := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex R C
  let bC : Module.Basis ι R C := Module.Free.chooseBasis R C
  let u : ι → n → K := fun k => (bC k : n → K)
  have huli : LinearIndependent K u := by
    have hR : LinearIndependent R u := bC.linearIndependent.map' C.subtype (Submodule.ker_subtype C)
    refine (LinearIndependent.iff_fractionRing R K).mp hR
  obtain ⟨N, hN0, hN⟩ := hfull
  have hAN : A N ≠ 0 := (map_ne_zero_iff A hA).mpr hN0
  have hsingle : ∀ i, (A N) • (Pi.single i (1 : K) : n → K) ∈ C := by
    intro i
    rw [hCmem]
    have h := hN (Matrix.single i j₀ 1)
    rw [map_single_one] at h
    convert h using 1
    ext l k
    simp only [colMat_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, Matrix.smul_apply, Matrix.single_apply]
    if hk : k = j₀ then
      if hl : l = i then
        subst hk
        subst hl
        simp
      else
        have hl' : i ≠ l := Ne.symm hl
        simp [hk, hl, hl']
    else
      have hk' : j₀ ≠ k := Ne.symm hk
      simp [hk, hk']
  have hCspan : ∀ c ∈ C, c ∈ Submodule.span K (Set.range u) := by
    intro c hc
    have : c = ∑ k, (bC.repr ⟨c, hc⟩ k) • u k := by
      have h1 : (((∑ k, (bC.repr ⟨c, hc⟩ k) • bC k : C)) : n → K) = c :=
        congrArg Subtype.val (bC.sum_repr ⟨c, hc⟩)
      rw [Submodule.coe_sum] at h1
      refine h1.symm
    rw [this]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [← algebraMap_smul K]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have huspan : ⊤ ≤ Submodule.span K (Set.range u) := by
    rw [← (Pi.basisFun K n).span_eq, Submodule.span_le]
    intro _ hx
    obtain ⟨i, hx⟩ := hx
    rw [← hx]
    have h := hCspan _ (hsingle i)
    rw [Pi.basisFun_apply]
    have e : (Pi.single i (1 : K) : n → K) = (A N)⁻¹ • ((A N) • (Pi.single i (1 : K) : n → K)) := by
      rw [smul_smul, inv_mul_cancel₀ hAN, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ h
  let bK : Module.Basis ι K (n → K) := Module.Basis.mk huli huspan
  have hcard : Fintype.card ι = Fintype.card n := by
    rw [← Module.finrank_eq_card_basis bK, Module.finrank_pi]
  let e : ι ≃ n := Fintype.equivOfCardEq hcard
  let bK' : Module.Basis n K (n → K) := bK.reindex e
  have hbK' : ∀ j, bK' j = u (e.symm j) := fun j => by
    rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]
  let g : Matrix n n K := (Pi.basisFun K n).toMatrix bK'
  have hg : ∀ i j, g i j = u (e.symm j) i := fun i j => by
    show (Pi.basisFun K n).toMatrix bK' i j = _
    rw [Module.Basis.toMatrix_apply, Pi.basisFun_repr, hbK']
  let _ : Invertible g := (Pi.basisFun K n).invertibleToMatrix bK'
  let G : GL n K := unitOfInvertible g
  have hGval : (G : Matrix n n K) = g := rfl
  have hmulVec : ∀ w : n → K, g.mulVec w = ∑ j, w j • u (e.symm j) := by
    intro w
    ext i
    simp only [Matrix.mulVec, dotProduct, hg, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hCiff : ∀ c : n → K, c ∈ C ↔ ∀ i, (((G⁻¹ : GL n K) : Matrix n n K).mulVec c) i ∈ A.range := by
    intro c
    constructor
    ·
      intro hc
      set r : ι → R := fun k => bC.repr ⟨c, hc⟩ k with hr
      have hc' : c = g.mulVec (fun j => A (r (e.symm j))) := by
        rw [hmulVec]
        have : c = ∑ k, r k • u k := by
          have h1 : (((∑ k, (bC.repr ⟨c, hc⟩ k) • bC k : C)) : n → K) = c :=
            congrArg Subtype.val (bC.sum_repr ⟨c, hc⟩)
          rw [Submodule.coe_sum] at h1
          refine h1.symm
        rw [this, ← e.symm.sum_comp]
        exact Finset.sum_congr rfl fun j _ => (algebraMap_smul K _ _).symm
      intro i
      rw [hc', Matrix.mulVec_mulVec, ← hGval, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      exact ⟨_, rfl⟩
    ·
      intro h
      choose r hr using h
      have hc' : c = g.mulVec (((G⁻¹ : GL n K) : Matrix n n K).mulVec c) := by
        rw [Matrix.mulVec_mulVec, ← hGval, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      rw [hc', hmulVec]
      refine C.sum_mem fun j _ => ?_
      rw [← hr j, algebraMap_smul]
      exact C.smul_mem _ (bC (e.symm j)).2
  refine ⟨G, fun x => ?_⟩
  rw [hcol]
  constructor
  ·
    intro h i j
    have hc := (hCiff _).mp (h j) i
    simp [Matrix.mul_apply]
    refine hc
  ·
    intro h j
    refine (hCiff _).mpr fun i => ?_
    have hc := h i j
    simp [Matrix.mulVec, dotProduct]
    refine hc


-- created on 2026-10-20
