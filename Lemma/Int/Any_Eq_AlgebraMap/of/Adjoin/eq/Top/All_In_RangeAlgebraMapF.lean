import Mathlib
import sympy.Basic

open Polynomial
open scoped TensorProduct

/--
[AlgEquiv_exists_extend_of_forall_isAlgebraic_mem_range_of_adjoin_range_eq_top](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgEquiv_exists_extend_of_forall_isAlgebraic_mem_range_of_adjoin_range_eq_top.lean)
-/

private lemma natDegree_minpoly_eq
  {κ : Type u₁} [Field κ]
  {K : Type*} [Field K] [Algebra κ K]
  {E : Type*} [Field E] [Algebra K E] [Algebra κ E] [IsScalarTower κ K E]
  (halgK : ∀ x : K, IsAlgebraic κ x → x ∈ Set.range (algebraMap κ K))
  {b : E} (hb : IsIntegral κ b) :
  (minpoly K b).natDegree = (minpoly κ b).natDegree := by
  set m := minpoly κ b with hm
  set q := minpoly K b with hq
  have hbK : IsIntegral K b := hb.tower_top
  have hdvd : q ∣ m.map (algebraMap κ K) := minpoly.dvd_map_of_isScalarTower κ K b
  have hcoef : ∀ i, q.coeff i ∈ Set.range (algebraMap κ K) := fun i =>
    halgK _ (isIntegral_coeff_of_dvd m q (minpoly.monic hb) (minpoly.monic hbK) hdvd i).isAlgebraic
  have hlifts : q ∈ Polynomial.lifts (algebraMap κ K) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    exact hcoef i
  obtain ⟨q₀, hq₀q, hq₀deg, hq₀mon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts (minpoly.monic hbK)
  have hdvd₀ : q₀ ∣ m := by
    rwa [← Polynomial.map_dvd_map (algebraMap κ K) (algebraMap κ K).injective hq₀mon, hq₀q]
  have hirr : Irreducible m := minpoly.irreducible hb
  obtain ⟨r, hr⟩ := hdvd₀
  have hq₀nu : ¬ IsUnit q₀ := by
    intro hu
    have h1 : q₀.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    have h2 : 0 < q.natDegree := minpoly.natDegree_pos hbK
    omega
  have hru : IsUnit r := (hirr.isUnit_or_isUnit hr).resolve_left hq₀nu
  have hrdeg : r.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hru
  have hr0 : r ≠ 0 := hru.ne_zero
  have hq₀0 : q₀ ≠ 0 := hq₀mon.ne_zero
  have : m.natDegree = q₀.natDegree + r.natDegree := by rw [hr, Polynomial.natDegree_mul hq₀0 hr0]
  rw [← hq₀deg, this, hrdeg, add_zero]

private lemma halg_fieldRange
  {κ : Type u₁} [Field κ]
  {F : Type u₂} [Field F] [Algebra κ F]
  {F' : Type u₄} [Field F'] [Algebra F F'] [Algebra κ F'] [IsScalarTower κ F F']
  (halg : ∀ x : F, IsAlgebraic κ x → x ∈ Set.range (algebraMap κ F))
  (x : ↥(IsScalarTower.toAlgHom κ F F').fieldRange) (hx : IsAlgebraic κ x) :
  x ∈ Set.range (algebraMap κ ↥(IsScalarTower.toAlgHom κ F F').fieldRange) := by
  let e : AlgEquiv κ F ↥(IsScalarTower.toAlgHom κ F F').fieldRange := AlgEquiv.ofInjectiveField _
  have hx' : IsAlgebraic κ (e.symm x) := (isAlgebraic_algHom_iff e.symm.toAlgHom e.symm.injective).mpr hx
  obtain ⟨c, hc⟩ := halg _ hx'
  refine ⟨c, e.symm.injective ?_⟩
  rwa [AlgEquiv.commutes]

private lemma linearDisjoint
  {κ : Type u₁} [Field κ]
  {F : Type u₂} [Field F] [Algebra κ F]
  {κ' : Type u₃} [Field κ'] [Algebra κ κ'] [Algebra.IsAlgebraic κ κ'] [Algebra.IsSeparable κ κ']
  {F' : Type u₄} [Field F'] [Algebra F F'] [Algebra κ F'] [Algebra κ' F'] [IsScalarTower κ F F'] [IsScalarTower κ κ' F']
  (halg : ∀ x : F, IsAlgebraic κ x → x ∈ Set.range (algebraMap κ F)) :
  (IsScalarTower.toAlgHom κ F F').fieldRange.toSubalgebra.LinearDisjoint
    (IsScalarTower.toAlgHom κ κ' F').range := by
  classical
  let fa := IsScalarTower.toAlgHom κ F F'
  let fb := IsScalarTower.toAlgHom κ κ' F'
  let A : IntermediateField κ F' := fa.fieldRange
  have : Algebra.IsIntegral κ ↥fb.range := by
    refine ⟨?_⟩
    rintro ⟨_, c, rfl⟩
    exact (isIntegral_algHom_iff fb.range.val Subtype.val_injective).mp
      ((Algebra.IsIntegral.isIntegral (R := κ) c).map fb)
  refine Subalgebra.LinearDisjoint.of_linearDisjoint_finite_right _ _ fun B' hB' hfin => ?_
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := κ) (M := ↥B')
  have hsj : ∀ j, ∃ c : κ', fb c = (s j : F') := fun j => by
    obtain ⟨c, hc⟩ := hB' (s j).2
    exact ⟨c, hc⟩
  choose c hc using hsj
  let S : Set κ' := Set.range c
  have : Finite S := Set.finite_range c |>.to_subtype
  let K₀ : IntermediateField κ κ' := IntermediateField.adjoin κ S
  have : FiniteDimensional κ K₀ :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have : Algebra.IsSeparable κ K₀ := Algebra.isSeparable_tower_bot_of_isSeparable κ K₀ κ'
  obtain ⟨α, hα⟩ := Field.exists_primitive_element κ K₀
  let β : κ' := (α : κ')
  have hβ : IsIntegral κ β := Algebra.IsIntegral.isIntegral β
  have hcj : ∀ j, c j ∈ Algebra.adjoin κ ({β} : Set κ') := fun j => by
    have h1 : (⟨c j, IntermediateField.subset_adjoin κ S ⟨j, rfl⟩⟩ : K₀) ∈ (⊤ : IntermediateField κ K₀) := trivial
    rw [← hα] at h1
    have h2 : c j ∈ (IntermediateField.adjoin κ ({α} : Set K₀)).map K₀.val := ⟨_, h1, rfl⟩
    rw [IntermediateField.adjoin_map] at h2
    have h3 : (K₀.val : K₀ → κ') '' {α} = {β} := by simp [β]
    rw [h3] at h2
    have h4 : c j ∈ (IntermediateField.adjoin κ ({β} : Set κ')).toSubalgebra :=
      (IntermediateField.mem_toSubalgebra _ _).mpr h2
    rwa [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hβ.isAlgebraic] at h4
  let b : F' := fb β
  have hb : IsIntegral κ b := hβ.map fb
  have hB'le : B' ≤ Algebra.adjoin κ ({b} : Set F') := by
    intro y hy
    have hy' : (⟨y, hy⟩ : ↥B') ∈ Submodule.span κ (Set.range s) := by rw [hs]; trivial
    have himg : y ∈ Submodule.span κ (Set.range (fun j => (s j : F'))) := by
      have h := Submodule.mem_map_of_mem (f := B'.val.toLinearMap) hy'
      rwa [Submodule.map_span, ← Set.range_comp] at h
    exact (by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      show (s j : F') ∈ Algebra.adjoin κ ({b} : Set F')
      rwa [← hc j, show ({b} : Set F') = fb '' {β} by simp [b], ← AlgHom.map_adjoin]) himg
  refine Subalgebra.LinearDisjoint.of_le_right_of_flat (B := Algebra.adjoin κ ({b} : Set F')) ?_ hB'le
  let pb := Algebra.adjoin.powerBasis hb
  refine Subalgebra.LinearDisjoint.of_basis_right _ _ pb.basis ?_
  have hdeg : (minpoly (↥A) b).natDegree = (minpoly κ b).natDegree :=
    natDegree_minpoly_eq (K := ↥A) (E := F') (halg_fieldRange halg) hb
  have key := linearIndependent_pow (K := ↥A) b
  rw [hdeg] at key
  have hfun : ((Algebra.adjoin κ ({b} : Set F')).val ∘ pb.basis : Fin pb.dim → F') =
      fun i : Fin (minpoly κ b).natDegree => b ^ (i : ℕ) := by
    funext i
    show ((pb.basis i : ↥(Algebra.adjoin κ ({b} : Set F'))) : F') = b ^ (i : ℕ)
    rw [pb.basis_eq_pow i, SubmonoidClass.coe_pow, Algebra.adjoin.powerBasis_gen]
  rwa [hfun]

@[path]
private lemma main
  {κ : Type u₁} [Field κ]
  {F : Type u₂} [Field F] [Algebra κ F]
  {κ' : Type u₃} [Field κ'] [Algebra κ κ'] [Algebra.IsAlgebraic κ κ'] [Algebra.IsSeparable κ κ']
  {F' : Type u₄} [Field F'] [Algebra F F'] [Algebra κ F'] [Algebra κ' F'] [IsScalarTower κ F F'] [IsScalarTower κ κ' F']
-- given
  (halg : ∀ x : F, IsAlgebraic κ x → x ∈ Set.range (algebraMap κ F))
  (hgen : Algebra.adjoin F (Set.range (algebraMap κ' F')) = ⊤)
  (σ : AlgEquiv κ F F) :
-- imply
  ∃ σ' : AlgEquiv κ' F' F', ∀ f : F, σ' (algebraMap F F' f) = algebraMap F F' (σ f) := by
-- proof
  classical
  let fa := IsScalarTower.toAlgHom κ F F'
  let fb := IsScalarTower.toAlgHom κ κ' F'
  let i : AlgHom κ (TensorProduct κ F κ') F' := Algebra.TensorProduct.productMap fa fb
  have hi_tmul : ∀ (f : F) (c : κ'), i (TensorProduct.tmul f c) = algebraMap F F' f * algebraMap κ' F' c := fun f c => by
    simp [i, fa, fb, Algebra.TensorProduct.productMap_apply_tmul]
  have hinj : Function.Injective i := by
    have H := linearDisjoint (κ' := κ') (F' := F') halg
    rw [Subalgebra.linearDisjoint_iff_injective] at H
    let e₁ : AlgEquiv κ F ↥fa.fieldRange.toSubalgebra := AlgEquiv.ofInjective fa fa.injective
    let e₂ : AlgEquiv κ κ' ↥fb.range := AlgEquiv.ofInjective fb fb.injective
    have hcomp : (i : TensorProduct κ F κ' → F') =
        (fa.fieldRange.toSubalgebra.mulMap fb.range) ∘ (Algebra.TensorProduct.congr e₁ e₂) := by
      funext x
      induction x using TensorProduct.inductionOn with
      | tmul f c =>
        rw [hi_tmul, Function.comp_apply, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
        rfl
      | add x y hx hy =>
        simp only [map_add, Function.comp_apply] at hx hy ⊢
        rw [hx, hy]
    rw [hcomp]
    exact H.comp (Algebra.TensorProduct.congr e₁ e₂).injective
  have hsurj : Function.Surjective i := by
    let R : Subalgebra F F' :=
      { carrier := Set.range i
        mul_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x * y, map_mul i x y⟩
        add_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x + y, map_add i x y⟩
        algebraMap_mem' := fun f => ⟨TensorProduct.tmul f (1 : κ'), by rw [hi_tmul, map_one, mul_one]⟩ }
    have hR : (⊤ : Subalgebra F F') ≤ R := by
      rw [← hgen, Algebra.adjoin_le_iff]
      rintro _ ⟨c, rfl⟩
      exact ⟨TensorProduct.tmul (1 : F) c, by rw [hi_tmul, map_one, one_mul]⟩
    intro y
    obtain ⟨x, hx⟩ := hR (Algebra.mem_top : y ∈ (⊤ : Subalgebra F F'))
    exact ⟨x, hx⟩
  let e : AlgEquiv κ (TensorProduct κ F κ') F' := AlgEquiv.ofBijective i ⟨hinj, hsurj⟩
  have he : ∀ x, e x = i x := fun x => rfl
  let τ : AlgEquiv κ F' F' := e.symm.trans ((Algebra.TensorProduct.congr σ (AlgEquiv.refl : AlgEquiv κ κ' κ')).trans e)
  have hτ : ∀ x, τ (i x) = i (Algebra.TensorProduct.congr σ (AlgEquiv.refl : AlgEquiv κ κ' κ') x) := fun x => by
    show e (Algebra.TensorProduct.congr σ AlgEquiv.refl (e.symm (i x))) = _
    rw [← he x, e.symm_apply_apply, he]
  have hτb : ∀ c : κ', τ (algebraMap κ' F' c) = algebraMap κ' F' c := fun c => by
    have h1 : algebraMap κ' F' c = i (TensorProduct.tmul (1 : F) c) := by rw [hi_tmul, map_one, one_mul]
    rw [h1, hτ, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
    simp
  let σ' : AlgEquiv κ' F' F' := AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) hτb
  refine ⟨σ', fun f => ?_⟩
  show τ (algebraMap F F' f) = algebraMap F F' (σ f)
  have h1 : algebraMap F F' f = i (TensorProduct.tmul f (1 : κ')) := by rw [hi_tmul, map_one, mul_one]
  rw [h1, hτ, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  show i (TensorProduct.tmul (σ f) (1 : κ')) = algebraMap F F' (σ f)
  rw [hi_tmul, map_one, mul_one]


-- created on 2026-10-09
