import Mathlib
import Lemma.AffineDilatation.Basic
import sympy.Basic

open scoped nonZeroDivisors
open AffineDilatation

/--
[AffineDilatation_nonempty_algHom_and_subsingleton_of_isSMulRegular](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AffineDilatation_nonempty_algHom_and_subsingleton_of_isSMulRegular.lean)
-/

private lemma algHom_ext
  {A : Type u}
  [CommRing A]
  {C : Type v}
  [CommRing C]
  [Algebra A C]
  (I : Ideal A) (a : A) (hreg : IsSMulRegular C a) (φ ψ : AlgHom A (Ring I a) C) :
  φ = ψ := by
  apply AlgHom.ext
  rintro ⟨x, hx⟩
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      change φ (divElem I a g hg) = ψ (divElem I a g hg)
      have h := congrArg φ (algebraMap_mul_divElem I a g hg)
      have h' := congrArg ψ (algebraMap_mul_divElem I a g hg)
      rw [map_mul, φ.commutes, φ.commutes] at h
      rw [map_mul, ψ.commutes, ψ.commutes] at h'
      refine hreg (?_ : a • φ (divElem I a g hg) = a • ψ (divElem I a g hg))
      rw [Algebra.smul_def, Algebra.smul_def, h, h']
  | algebraMap r =>
      exact (φ.commutes r).trans (ψ.commutes r).symm
  | add x y hx hy ihx ihy =>
      have : (⟨x + y, Subalgebra.add_mem _ hx hy⟩ : Ring I a) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [this, map_add, map_add, ihx, ihy]
  | mul x y hx hy ihx ihy =>
      have : (⟨x * y, Subalgebra.mul_mem _ hx hy⟩ : Ring I a) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [this, map_mul, map_mul, ihx, ihy]

private lemma subsingleton_algHom
  {A : Type u}
  [CommRing A]
  {C : Type v}
  [CommRing C]
  [Algebra A C]
  (I : Ideal A) (a : A) (hreg : IsSMulRegular C a) :
  Subsingleton (AlgHom A (Ring I a) C) :=
  ⟨algHom_ext I a hreg⟩

private lemma nonempty_algHom
  {A : Type u}
  [CommRing A]
  {C : Type v}
  [CommRing C]
  [Algebra A C]
  (I : Ideal A) (a : A) (hreg : IsSMulRegular C a)
  (hI : I.map (algebraMap A C) ≤ Ideal.span {algebraMap A C a}) :
  Nonempty (AlgHom A (Ring I a) C) := by
  classical
  set b : C := algebraMap A C a with hb
  let Ca := Localization.Away b
  let j : RingHom C Ca := algebraMap C Ca
  have hj : Function.Injective j := by
    refine IsLocalization.injective Ca (M := Submonoid.powers b) ?_
    rw [Submonoid.powers_le]
    rw [mem_nonZeroDivisors_iff_right]
    intro c hc
    refine hreg (?_ : a • c = a • (0 : C))
    rwa [Algebra.smul_def, Algebra.smul_def, mul_zero, mul_comm]
  have hunit : IsUnit ((j.comp (algebraMap A C)) a) := by
    change IsUnit (j b)
    exact IsLocalization.Away.algebraMap_isUnit b
  let Φ : RingHom (Localization.Away a) Ca := IsLocalization.Away.lift a hunit
  have hΦalg : ∀ g : A, Φ (algebraMap A (Localization.Away a) g) = j (algebraMap A C g) := by
    intro g
    exact IsLocalization.Away.lift_eq a hunit g
  have hΦmk : ∀ g : A, Φ (IsLocalization.mk' (Localization.Away a) g (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a)) * j b = j (algebraMap A C g) := by
    intro g
    have h := IsLocalization.mk'_spec (Localization.Away a) g (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a)
    have h' := congrArg Φ h
    rwa [map_mul, hΦalg, hΦalg] at h'
  have hrange : ∀ x ∈ subalgebra I a, Φ x ∈ j.range := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
        obtain ⟨g, hg, rfl⟩ := hx
        have hgC : algebraMap A C g ∈ Ideal.span {b} := hI (Ideal.mem_map_of_mem _ hg)
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hgC
        refine ⟨c, ?_⟩
        have h1 := hΦmk g
        rw [← hc, map_mul] at h1
        exact ((IsLocalization.Away.algebraMap_isUnit b).mul_left_injective h1).symm
    | algebraMap r => exact ⟨algebraMap A C r, (hΦalg r).symm⟩
    | add x y _ _ ihx ihy =>
        rw [map_add]
        exact Subring.add_mem _ ihx ihy
    | mul x y _ _ ihx ihy =>
        rw [map_mul]
        exact Subring.mul_mem _ ihx ihy
  let e : RingEquiv C j.range := RingEquiv.ofBijective j.rangeRestrict ⟨fun x y h => hj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective j⟩
  let ΦD : RingHom (Ring I a) j.range := (Φ.comp (subalgebra I a).val.toRingHom).codRestrict j.range (fun x => hrange x.1 x.2)
  let φ : RingHom (Ring I a) C := e.symm.toRingHom.comp ΦD
  have hφ : ∀ x : Ring I a, j (φ x) = Φ x := by
    intro x
    exact congrArg Subtype.val (e.apply_symm_apply (ΦD x))
  refine ⟨{ φ with commutes' := ?_ }⟩
  intro g
  apply hj
  change j (φ (algebraMap A (Ring I a) g)) = j (algebraMap A C g)
  rw [hφ]
  exact hΦalg g

@[path]
private lemma main
  {A : Type u} [CommRing A]
  {C : Type v} [CommRing C] [Algebra A C]
  {I : Ideal A} {a : A}
-- given
  (hreg : IsSMulRegular C a)
  (hI : I.map (algebraMap A C) ≤ Ideal.span {algebraMap A C a}) :
-- imply
  Nonempty (AlgHom A (AffineDilatation.Ring I a) C) ∧
    Subsingleton (AlgHom A (AffineDilatation.Ring I a) C) :=
-- proof
  ⟨nonempty_algHom I a hreg hI,
    subsingleton_algHom I a hreg⟩

-- created on 2026-10-09
