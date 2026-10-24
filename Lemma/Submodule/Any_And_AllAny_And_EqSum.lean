import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private noncomputable def intClosureIn {Ω : Type u} [Field Ω] (R : Subring Ω) (F : Subfield Ω) : Subring Ω where
  carrier := {x | x ∈ F ∧ IsIntegral ↥R x}
  zero_mem' := ⟨zero_mem _, isIntegral_zero⟩
  one_mem' := ⟨one_mem _, isIntegral_one⟩
  add_mem' := fun hx hy => ⟨add_mem hx.1 hy.1, hx.2.add hy.2⟩
  neg_mem' := fun hx => ⟨neg_mem hx.1, hx.2.neg⟩
  mul_mem' := fun hx hy => ⟨mul_mem hx.1 hy.1, hx.2.mul hy.2⟩
private lemma mem_intClosureIn {Ω : Type u} [Field Ω] {R : Subring Ω} {F : Subfield Ω} {x : Ω} : x ∈ intClosureIn R F ↔ x ∈ F ∧ IsIntegral ↥R x := Iff.rfl
/--
[Subfield_exists_finset_subset_forall_eq_sum_mul_of_isIntegral_of_span](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Subfield_exists_finset_subset_forall_eq_sum_mul_of_isIntegral_of_span.lean)
-/
@[path]
private lemma main
  {Ω : Type u} [Field Ω] [CharZero Ω]
  (R : Subring Ω)
  (F₀ L : Subfield Ω)
  (N B : Set Ω)
  (s u : Finset Ω)
  -- given
  (hR : IsNoetherianRing ↥R)
  (hRF : R ≤ F₀.toSubring)
  (hFL : F₀ ≤ L)
  (hfrac : ∀ x ∈ F₀, ∃ r ∈ R, ∃ d ∈ R, d ≠ 0 ∧ x * d = r)
  (hN : ∀ x, x ∈ N ↔ x ∈ F₀ ∧ IsIntegral ↥R x)
  (hB : ∀ x, x ∈ B ↔ x ∈ L ∧ IsIntegral ↥R x)
  (hs : ∀ x ∈ N, x ∈ Submodule.span ↥R (↑s : Set Ω))
  (hu : ∀ x ∈ L, x ∈ Submodule.span ↥F₀ (↑u : Set Ω)) :
  -- imply
  ∃ t : Finset Ω, (↑t : Set Ω) ⊆ B ∧ ∀ x ∈ B, ∃ f : Ω → Ω, (∀ c ∈ t, f c ∈ N) ∧ x = ∑ c ∈ t, f c * c := by
  -- proof
  classical
  let _ := hR
  let N' : Subring Ω := intClosureIn R F₀
  let B' : Subring Ω := intClosureIn R L
  have hNN' : ∀ x, x ∈ N ↔ x ∈ N' := fun x => hN x
  have hBB' : ∀ x, x ∈ B ↔ x ∈ B' := fun x => hB x
  have hFL' : F₀.toSubring ≤ L.toSubring := hFL
  have hRN : R ≤ N' := fun x hx => ⟨hRF hx, isIntegral_algebraMap (R := ↥R) (A := Ω) (x := ⟨x, hx⟩)⟩
  have hNF : N' ≤ F₀.toSubring := fun _ hx => hx.1
  have hNB : N' ≤ B' := fun _ hx => ⟨hFL hx.1, hx.2⟩
  have hBL : B' ≤ L.toSubring := fun _ hx => hx.1
  let iRN : Algebra ↥R ↥N' := (Subring.inclusion hRN).toAlgebra
  let iNF : Algebra ↥N' ↥F₀ := (Subring.inclusion hNF).toAlgebra
  let iNB : Algebra ↥N' ↥B' := (Subring.inclusion hNB).toAlgebra
  let iBL : Algebra ↥B' ↥L := (Subring.inclusion hBL).toAlgebra
  let iFL : Algebra ↥F₀ ↥L := (Subring.inclusion hFL').toAlgebra
  let iNL : Algebra ↥N' ↥L := (Subring.inclusion (hNF.trans hFL')).toAlgebra
  let iRL : Algebra ↥R ↥L := (Subring.inclusion (hRF.trans hFL')).toAlgebra
  let _ : IsScalarTower ↥N' ↥F₀ ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let _ : IsScalarTower ↥N' ↥B' ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let _ : IsScalarTower ↥R ↥N' ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let tRNΩ : IsScalarTower ↥R ↥N' Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let tRLΩ : IsScalarTower ↥R ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let tNLΩ : IsScalarTower ↥N' ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let tNFΩ : IsScalarTower ↥N' ↥F₀ Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let tFLΩ : IsScalarTower ↥F₀ ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have intN_L : ∀ x : ↥L, IsIntegral ↥N' x ↔ IsIntegral ↥N' (x : Ω) := fun x => (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥N' ↥L Ω) Subtype.val_injective).symm
  have intN_F : ∀ x : ↥F₀, IsIntegral ↥N' x ↔ IsIntegral ↥N' (x : Ω) := fun x => (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥N' ↥F₀ Ω) Subtype.val_injective).symm
  let hNint : Algebra.IsIntegral ↥R ↥N' := ⟨fun y => (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥R ↥N' Ω) Subtype.val_injective).mp y.2.2⟩
  have intR_of_intN : ∀ x : Ω, IsIntegral ↥N' x → IsIntegral ↥R x := fun x hx => isIntegral_trans x hx
  have intN_of_intR : ∀ x : Ω, IsIntegral ↥R x → IsIntegral ↥N' x := fun x hx => hx.tower_top
  let hNfin : Module.Finite ↥R ↥N' := by
    let M : Submodule ↥R Ω := Submodule.span ↥R (↑s : Set Ω)
    let _ : IsNoetherian ↥R ↥M := isNoetherian_of_fg_of_noetherian M (Submodule.fg_span s.finite_toSet)
    let ι : ↥N' →ₗ[↥R] ↥M :=
      { toFun := fun x => ⟨(x : Ω), hs x ((hNN' x).mpr x.2)⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hι : Function.Injective ι := fun x y h => Subtype.ext (show (x : Ω) = y from congrArg (fun m : ↥M => (m : Ω)) h)
    refine Module.Finite.of_injective ι hι
  let hNnoeth : IsNoetherianRing ↥N' := by
    let _ : Algebra.FiniteType ↥R ↥N' := Module.Finite.finiteType ↥N'
    apply Algebra.FiniteType.isNoetherianRing ↥R ↥N'
  let hNF₀ : IsFractionRing ↥N' ↥F₀ := by
    refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
    ·
      intro yunit
      obtain ⟨y, hy⟩ := yunit
      apply isUnit_iff_ne_zero.mpr
      intro h
      apply nonZeroDivisors.ne_zero hy
      apply Subtype.ext (show (y : Ω) = 0 from congrArg (fun z : ↥F₀ => (z : Ω)) h)
    ·
      intro zpair
      obtain ⟨z, hz⟩ := zpair
      obtain ⟨r, hr, d, hd, hd0, hzd⟩ := hfrac z hz
      refine ⟨(⟨r, hRN hr⟩, ⟨⟨d, hRN hd⟩, mem_nonZeroDivisors_of_ne_zero (fun h => hd0 (congrArg Subtype.val h))⟩), ?_⟩
      apply Subtype.ext hzd
    ·
      intro x y h
      have hxy : x = y := Subtype.ext (show (x : Ω) = y from congrArg (fun z : ↥F₀ => (z : Ω)) h)
      refine ⟨1, ?_⟩
      rw [hxy]
  let hNic : IsIntegrallyClosed ↥N' := by
    refine (isIntegrallyClosed_iff ↥F₀).mpr fun {x} hx => ?_
    exact ⟨⟨(x : Ω), x.2, intR_of_intN _ ((intN_F x).mp hx)⟩, rfl⟩
  let hLfin : Module.Finite ↥F₀ ↥L := by
    let M : Submodule ↥F₀ Ω := Submodule.span ↥F₀ (↑u : Set Ω)
    let _ : IsNoetherian ↥F₀ ↥M := isNoetherian_of_fg_of_noetherian M (Submodule.fg_span u.finite_toSet)
    let ι : ↥L →ₗ[↥F₀] ↥M :=
      { toFun := fun x => ⟨(x : Ω), hu x x.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hι : Function.Injective ι := fun x y h => Subtype.ext (show (x : Ω) = y from congrArg (fun m : ↥M => (m : Ω)) h)
    refine Module.Finite.of_injective ι hι
  let _ : CharZero ↥F₀ := (algebraMap ↥F₀ Ω).charZero
  let _ : Algebra.IsSeparable ↥F₀ ↥L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  let hBic : IsIntegralClosure ↥B' ↥N' ↥L :=
    { algebraMap_injective := fun x y h => Subtype.ext (show (x : Ω) = y from congrArg (fun z : ↥L => (z : Ω)) h)
      isIntegral_iff := fun {x} => by
        constructor
        ·
          intro hx
          exact ⟨⟨(x : Ω), x.2, intR_of_intN _ ((intN_L x).mp hx)⟩, rfl⟩
        ·
          intro hy
          obtain ⟨y, rfl⟩ := hy
          apply (intN_L _).mpr (intN_of_intR _ y.2.2) }
  let hBfin : Module.Finite ↥N' ↥B' := IsIntegralClosure.finite ↥N' ↥F₀ ↥L ↥B'
  obtain ⟨t₀, ht₀⟩ := hBfin.fg_top
  let val : ↥B' →ₗ[↥N'] Ω :=
    { toFun := fun c => (c : Ω)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let t : Finset Ω := Finset.image (fun c : ↥B' => ((c : ↥B') : Ω)) t₀
  refine ⟨t, ?_, ?_⟩
  ·
    intro c hc
    obtain ⟨b, _, hbc⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hc)
    rw [← hbc]
    apply (hBB' _).mpr b.2
  ·
    intro x hxB
    have hxB' : x ∈ B' := (hBB' x).mp hxB
    have hmem : (⟨x, hxB'⟩ : ↥B') ∈ Submodule.span ↥N' (↑t₀ : Set ↥B') := by
      rw [ht₀]
      apply Submodule.mem_top
    have himg := Submodule.mem_map_of_mem (f := val) hmem
    rw [Submodule.map_span] at himg
    have hsub : (val '' (↑t₀ : Set ↥B')) ⊆ (↑t : Set Ω) := by
      intro y hy
      obtain ⟨b, hb, rfl⟩ := hy
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨b, Finset.mem_coe.mp hb, rfl⟩)
    have hx' : x ∈ Submodule.span ↥N' (↑t : Set Ω) := Submodule.span_mono hsub himg
    obtain ⟨f₀, hf₀⟩ := Submodule.mem_span_finset.mp hx'
    have hsum : ∑ i ∈ t, f₀ i • i = x := hf₀.2
    refine ⟨fun c => ((f₀ c : ↥N') : Ω), fun c _ => (hNN' _).mpr (f₀ c).2, ?_⟩
    rw [← hsum]
    refine Finset.sum_congr rfl fun c _ => ?_
    apply Algebra.smul_def (f₀ c) c


-- created on 2026-10-20
