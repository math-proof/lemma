import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.overlappingInstances false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false


variable (O : Type*) [Ring O]
private lemma includeRight_injective
  [Module.Free ℤ O] :
  Function.Injective
    (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] TensorProduct ℤ ℚ O) := by
  have h1 : Function.Injective ((Algebra.linearMap ℤ ℚ).rTensor O) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (fun x y hxy => by
      have : ((x : ℤ) : ℚ) = ((y : ℤ) : ℚ) := hxy
      exact_mod_cast this)
  have h2 : Function.Injective (TensorProduct.lid ℤ O).symm := (TensorProduct.lid ℤ O).symm.injective
  have heq : ∀ o : O,
      (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] TensorProduct ℤ ℚ O) o =
      ((Algebra.linearMap ℤ ℚ).rTensor O) ((TensorProduct.lid ℤ O).symm o) := fun o => by
    simp [Algebra.TensorProduct.includeRight_apply, LinearMap.rTensor_tmul]
  intro x y hxy
  rw [heq, heq] at hxy
  refine h2 (h1 hxy)
private lemma exists_nsmul_eq_one_tmul
  (x : TensorProduct ℤ ℚ O) :
  ∃ n : ℕ, n ≠ 0 ∧ ∃ o : O, (n : ℚ) • x = TensorProduct.tmul ℤ (1 : ℚ) o := by
  refine TensorProduct.inductionOn x ?_ ?_
  ·
    intro q o
    refine ⟨q.den, q.den_nz, q.num • o, ?_⟩
    rw [TensorProduct.smul_tmul', smul_eq_mul, Rat.den_mul_eq_num, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', Int.smul_one_eq_cast]
  ·
    intro x y hx hy
    obtain ⟨m, hm, u, hu⟩ := hx
    obtain ⟨n, hn, w, hw⟩ := hy
    refine ⟨m * n, mul_ne_zero hm hn, (n : ℤ) • u + (m : ℤ) • w, ?_⟩
    rw [smul_add, Nat.cast_mul, mul_comm (m : ℚ), mul_smul, hu, mul_comm (n : ℚ), mul_smul, hw,
      TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      TensorProduct.smul_tmul', TensorProduct.smul_tmul', TensorProduct.smul_tmul', Int.smul_one_eq_cast,
      Int.smul_one_eq_cast, Int.cast_natCast, Int.cast_natCast, smul_eq_mul, smul_eq_mul, mul_one, mul_one]
private lemma nontrivial
  [Module.Free ℤ O] [Nontrivial O] :
  Nontrivial (TensorProduct ℤ ℚ O) := by
  refine ⟨⟨(Algebra.TensorProduct.includeRight : O →ₐ[ℤ] TensorProduct ℤ ℚ O) 1,
    (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] TensorProduct ℤ ℚ O) 0, ?_⟩⟩
  refine fun h => one_ne_zero (includeRight_injective O h)
private lemma noZeroDivisors
  [Module.Free ℤ O] [NoZeroDivisors O] :
  NoZeroDivisors (TensorProduct ℤ ℚ O) := by
  refine ⟨fun {x y} hxy => ?_⟩
  obtain ⟨m, hm, u, hu⟩ := exists_nsmul_eq_one_tmul O x
  obtain ⟨n, hn, w, hw⟩ := exists_nsmul_eq_one_tmul O y
  have h : ((m : ℚ) • x) * ((n : ℚ) • y) = TensorProduct.tmul ℤ (1 : ℚ) (u * w) := by
    rw [hu, hw, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [smul_mul_smul_comm, hxy, smul_zero] at h
  have huw : u * w = 0 := by
    apply includeRight_injective O
    rw [map_zero, Algebra.TensorProduct.includeRight_apply, ← h]
  cases mul_eq_zero.mp huw
  ·
    rename_i h0
    left
    have : (m : ℚ) • x = 0 := by
      rw [hu, h0, TensorProduct.tmul_zero]
    refine (smul_eq_zero.mp this).resolve_left (Nat.cast_ne_zero.mpr hm)
  ·
    rename_i h0
    right
    have : (n : ℚ) • y = 0 := by
      rw [hw, h0, TensorProduct.tmul_zero]
    refine (smul_eq_zero.mp this).resolve_left (Nat.cast_ne_zero.mpr hn)
private lemma finrank_eq_and_isUnit
  [IsDomain O] [Module.Free ℤ O] [Module.Finite ℤ O]
  (hrank : Module.finrank ℤ O = 4) :
  Module.finrank ℚ (TensorProduct ℤ ℚ O) = 4 ∧ ∀ x : TensorProduct ℤ ℚ O, x ≠ 0 → IsUnit x := by
  let _ := nontrivial O
  let _ := noZeroDivisors O
  let _ : IsDomain (TensorProduct ℤ ℚ O) := NoZeroDivisors.to_isDomain _
  refine ⟨by rw [Module.finrank_baseChange, hrank], ?_⟩
  let _ := divisionRingOfFiniteDimensional ℚ (TensorProduct ℤ ℚ O)
  refine fun x hx => isUnit_iff_ne_zero.mpr hx
private lemma center_subset_range
  [IsDomain O] [Module.Free ℤ O] [Module.Finite ℤ O]
  (hrank : Module.finrank ℤ O = 4)
  (hnc : ∃ u w : O, u * w ≠ w * u) :
  ∀ z : TensorProduct ℤ ℚ O, (∀ x : TensorProduct ℤ ℚ O, z * x = x * z) →
    z ∈ Set.range (algebraMap ℚ (TensorProduct ℤ ℚ O)) := by
  classical
  let _ := nontrivial O
  let _ := noZeroDivisors O
  let _ : IsDomain (TensorProduct ℤ ℚ O) := NoZeroDivisors.to_isDomain _
  have hdim : Module.finrank ℚ (TensorProduct ℤ ℚ O) = 4 := by
    rw [Module.finrank_baseChange, hrank]
  let instD : DivisionRing (TensorProduct ℤ ℚ O) :=
    divisionRingOfFiniteDimensional ℚ (TensorProduct ℤ ℚ O)
  have hnc' : ∃ x y : TensorProduct ℤ ℚ O, x * y ≠ y * x := by
    obtain ⟨u, w, huw⟩ := hnc
    refine ⟨(Algebra.TensorProduct.includeRight : O →ₐ[ℤ] TensorProduct ℤ ℚ O) u,
      (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] TensorProduct ℤ ℚ O) w, fun h => huw ?_⟩
    apply includeRight_injective O
    rw [map_mul, map_mul, h]
  set Z : Subalgebra ℚ (TensorProduct ℤ ℚ O) := Subalgebra.center ℚ (TensorProduct ℤ ℚ O) with hZ
  have hZf : IsField ↥Z := by
    refine ⟨⟨0, 1, zero_ne_one⟩, fun x y => mul_comm x y, fun {x} hx => ?_⟩
    have hx0 : (x : TensorProduct ℤ ℚ O) ≠ 0 := fun h => hx (Subtype.ext h)
    have hxinv : (x : TensorProduct ℤ ℚ O)⁻¹ ∈ Z := by
      refine Subalgebra.mem_center_iff.mpr fun y => ?_
      have hc : (x : TensorProduct ℤ ℚ O) * y = y * x := (Subalgebra.mem_center_iff.mp x.2 y).symm
      calc
        _ = (x : TensorProduct ℤ ℚ O)⁻¹ * ((x : TensorProduct ℤ ℚ O) * y) *
            (x : TensorProduct ℤ ℚ O)⁻¹ := by
          rw [← mul_assoc, inv_mul_cancel₀ hx0, one_mul]
        _ = (x : TensorProduct ℤ ℚ O)⁻¹ * y := by
          rw [hc]
          simp only [mul_assoc, mul_inv_cancel₀ hx0, mul_one]
    refine ⟨⟨_, hxinv⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩
  let instZ : Field ↥Z := hZf.toField
  let _ : Module.Finite ↥Z (TensorProduct ℤ ℚ O) :=
    Module.Finite.of_restrictScalars_finite ℚ ↥Z (TensorProduct ℤ ℚ O)
  have htower : Module.finrank ℚ ↥Z * Module.finrank ↥Z (TensorProduct ℤ ℚ O) = 4 := by
    rw [Module.finrank_mul_finrank, hdim]
  have hspan : ∀ (x y : TensorProduct ℤ ℚ O), Module.finrank ↥Z (TensorProduct ℤ ℚ O) ≤ 2 →
      x * y = y * x := by
    intro x y h2
    if hxZ : x ∈ Z then
      refine (Subalgebra.mem_center_iff.mp hxZ y).symm
    else
      have hli : LinearIndependent ↥Z (Matrix.vecCons (1 : TensorProduct ℤ ℚ O)
        (Matrix.vecCons x Matrix.vecEmpty)) := by
        rw [LinearIndependent.pair_iff]
        intro s t hst
        if ht : t = 0 then
          simp only [ht, zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
          refine ⟨hst, ht⟩
        else
          exfalso
          apply hxZ
          have key : x = -((t⁻¹ * s : ↥Z) • (1 : TensorProduct ℤ ℚ O)) := by
            have := congrArg (fun v => (t⁻¹ : ↥Z) • v) hst
            simp only [smul_add, smul_smul, inv_mul_cancel₀ ht, one_smul, smul_zero] at this
            refine eq_neg_of_add_eq_zero_right this
          have hsm : ((t⁻¹ * s : ↥Z) • (1 : TensorProduct ℤ ℚ O)) =
              ((t⁻¹ * s : ↥Z) : TensorProduct ℤ ℚ O) := by
            change ((t⁻¹ * s : ↥Z) : TensorProduct ℤ ℚ O) * 1 = _
            rw [mul_one]
          rw [key, hsm]
          refine Z.neg_mem (SetLike.coe_mem _)
      have hcardle : Fintype.card (Fin 2) ≤ Module.finrank ↥Z (TensorProduct ℤ ℚ O) := by
        have this := hli.fintype_card_le_finrank
        simp at this
        refine this
      have h2card : Module.finrank ↥Z (TensorProduct ℤ ℚ O) ≤ Fintype.card (Fin 2) := by
        simp
        refine h2
      have hcard : Fintype.card (Fin 2) = Module.finrank ↥Z (TensorProduct ℤ ℚ O) :=
        le_antisymm hcardle h2card
      let bs := basisOfLinearIndependentOfCardEqFinrank hli hcard
      obtain ⟨c, hc⟩ : ∃ c : Fin 2 → ↥Z, y = ∑ i,
          c i • (Matrix.vecCons (1 : TensorProduct ℤ ℚ O) (Matrix.vecCons x Matrix.vecEmpty)) i :=
        ⟨fun i => bs.repr y i, by
          conv_lhs => rw [← bs.sum_repr y]
          simp only [bs, coe_basisOfLinearIndependentOfCardEqFinrank]⟩
      rw [hc]
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      have h0 : ∀ c : ↥Z, c • (1 : TensorProduct ℤ ℚ O) = (c : TensorProduct ℤ ℚ O) := fun c => by
        change (c : TensorProduct ℤ ℚ O) * 1 = _
        rw [mul_one]
      have h1 : ∀ c : ↥Z, c • x = (c : TensorProduct ℤ ℚ O) * x := fun c => rfl
      rw [h0, h1]
      have hc0 := Subalgebra.mem_center_iff.mp (c 0).2
      have hc1 := Subalgebra.mem_center_iff.mp (c 1).2
      rw [mul_add, add_mul, hc0 x, ← mul_assoc, hc1 x, mul_assoc]
  have hZ1 : Module.finrank ℚ ↥Z = 1 := by
    obtain ⟨x, y, hxy⟩ := hnc'
    have h3 : 3 ≤ Module.finrank ↥Z (TensorProduct ℤ ℚ O) := by
      by_contra h
      refine hxy (hspan x y (by omega))
    have hZpos : 0 < Module.finrank ℚ ↥Z := Module.finrank_pos
    have ha4 : Module.finrank ℚ ↥Z ≤ 4 := Nat.le_of_dvd (by norm_num) (Dvd.intro _ htower)
    generalize ha : Module.finrank ℚ ↥Z = A at htower hZpos ha4
    generalize hb : Module.finrank ↥Z (TensorProduct ℤ ℚ O) = B at htower h3
    interval_cases A
    all_goals omega
  intro z hz
  have hzZ : z ∈ Z := by
    rw [hZ, Subalgebra.mem_center_iff]
    refine fun y => (hz y).symm
  have hone : (⟨1, Z.one_mem⟩ : ↥Z) ≠ 0 := by
    intro h
    refine one_ne_zero (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨1, Z.one_mem⟩ : ↥Z) hone).mp hZ1 ⟨z, hzZ⟩
  refine ⟨c, ?_⟩
  have this := congrArg Subtype.val hc
  simp only [SetLike.val_smul] at this
  rw [← this, Algebra.algebraMap_eq_smul_one]
/--
[finrank_rat_tensorProduct_eq_four_and_forall_isUnit_and_forall_comm_mem_range](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_finrank_rat_tensorProduct_eq_four_and_forall_isUnit_and_forall_comm_mem_range.lean)
-/
@[path]
private lemma main
  (O : Type*) [Ring O] [IsDomain O] [Module.Free ℤ O] [Module.Finite ℤ O]
  (hrank : Module.finrank ℤ O = 4)
  (ℓ : ℕ) [Fact ℓ.Prime]
  (hℓ : Nonempty (AlgEquiv (PadicInt ℓ) (TensorProduct ℤ (PadicInt ℓ) O)
    (Matrix (Fin 2) (Fin 2) (PadicInt ℓ)))) :
  -- imply
  Module.finrank ℚ (TensorProduct ℤ ℚ O) = 4 ∧
    (∀ x : TensorProduct ℤ ℚ O, x ≠ 0 → IsUnit x) ∧
    (∀ z : TensorProduct ℤ ℚ O, (∀ x : TensorProduct ℤ ℚ O, z * x = x * z) →
      z ∈ Set.range (algebraMap ℚ (TensorProduct ℤ ℚ O))) := by
  -- proof
  classical
  have hnc : ∃ u w : O, u * w ≠ w * u := by
    by_contra hall
    push Not at hall
    obtain ⟨φ⟩ := hℓ
    have hcomm : ∀ s t : TensorProduct ℤ (PadicInt ℓ) O, s * t = t * s := by
      intro s t
      refine TensorProduct.inductionOn s ?_ ?_
      ·
        intro c u
        refine TensorProduct.inductionOn t ?_ ?_
        ·
          intro d w
          rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_comm c d,
            hall u w]
        ·
          intro x y hx hy
          rw [mul_add, add_mul, hx, hy]
      ·
        intro x y hx hy
        rw [add_mul, mul_add, hx, hy]
    have hM : ∀ A B : Matrix (Fin 2) (Fin 2) (PadicInt ℓ), A * B = B * A := fun A B => by
      have this := hcomm (φ.symm A) (φ.symm B)
      have hφ := congrArg φ this
      simp at hφ
      refine hφ
    let A01 : Matrix (Fin 2) (Fin 2) (PadicInt ℓ) :=
      Matrix.vecCons (Matrix.vecCons 0 (Matrix.vecCons 1 Matrix.vecEmpty))
        (Matrix.vecCons (Matrix.vecCons 0 (Matrix.vecCons 0 Matrix.vecEmpty)) Matrix.vecEmpty)
    let A10 : Matrix (Fin 2) (Fin 2) (PadicInt ℓ) :=
      Matrix.vecCons (Matrix.vecCons 0 (Matrix.vecCons 0 Matrix.vecEmpty))
        (Matrix.vecCons (Matrix.vecCons 1 (Matrix.vecCons 0 Matrix.vecEmpty)) Matrix.vecEmpty)
    have h := hM A01 A10
    have h00 := congrFun (congrFun h 0) 0
    rw [Matrix.mul_apply, Matrix.mul_apply] at h00
    simp [Fin.sum_univ_two, A01, A10, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] at h00
  obtain ⟨h1, h2⟩ := finrank_eq_and_isUnit O hrank
  refine ⟨h1, h2, center_subset_range O hrank hnc⟩


-- created on 2026-10-21
