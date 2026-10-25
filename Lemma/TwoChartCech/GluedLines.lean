import Lemma.AlgebraicGeometry.TwoChartCech
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Algebra.Subalgebra.Prod
import Abbrev.TwoChartCech_GluedLines

set_option autoImplicit false

noncomputable section

open LaurentPolynomial

universe u

namespace TwoChartCech

variable (R : Type u) [CommRing R] {s : ℕ}

def polyPart : Subalgebra R R[T;T⁻¹] where
  carrier := {f | ∀ n ∈ f.coeff.support, 0 ≤ n}
  mul_mem' := by
    intro f g hf hg n hn
    classical
    obtain ⟨i, hi, j, hj, rfl⟩ :=
      Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset f g hn)
    exact add_nonneg (hf i hi) (hg j hj)
  add_mem' := by
    intro f g hf hg n hn
    rw [AddMonoidAlgebra.coeff_add] at hn
    rcases Finset.mem_union.mp (Finsupp.support_add hn) with h | h
    exacts [hf n h, hg n h]
  algebraMap_mem' := by
    intro r n hn
    rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, AddMonoidAlgebra.coeff_single] at hn
    rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hn)]

def invPolyPart : Subalgebra R R[T;T⁻¹] where
  carrier := {f | ∀ n ∈ f.coeff.support, n ≤ 0}
  mul_mem' := by
    intro f g hf hg n hn
    classical
    obtain ⟨i, hi, j, hj, rfl⟩ :=
      Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset f g hn)
    exact add_nonpos (hf i hi) (hg j hj)
  add_mem' := by
    intro f g hf hg n hn
    rw [AddMonoidAlgebra.coeff_add] at hn
    rcases Finset.mem_union.mp (Finsupp.support_add hn) with h | h
    exacts [hf n h, hg n h]
  algebraMap_mem' := by
    intro r n hn
    rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, AddMonoidAlgebra.coeff_single] at hn
    rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hn)]

theorem mem_polyPart_iff {f : R[T;T⁻¹]} : f ∈ polyPart R ↔ ∀ n ∈ f.coeff.support, 0 ≤ n := Iff.rfl

theorem mem_invPolyPart_iff {f : R[T;T⁻¹]} :
    f ∈ invPolyPart R ↔ ∀ n ∈ f.coeff.support, n ≤ 0 := Iff.rfl

def gluedLinesOverlap (a b : Fin s → Rˣ) : Subalgebra R (R[T;T⁻¹] × R[T;T⁻¹]) where
  carrier := {f | ∀ i, levalUnit R (a i) f.1 = levalUnit R (b i) f.2}
  mul_mem' := by
    intro f g hf hg i
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, hf i, hg i]
  add_mem' := by
    intro f g hf hg i
    simp only [Prod.fst_add, Prod.snd_add, map_add, hf i, hg i]
  algebraMap_mem' := by
    intro r i
    simp [Prod.algebraMap_apply, LaurentPolynomial.algebraMap_apply, LaurentPolynomial.eval₂_C]

@[reducible] def gluedLinesCover (a b : Fin s → Rˣ) : Cover.{u, u} R where
  A0 := ↥(gluedLinesOverlap R a b ⊓ (polyPart R).prod (polyPart R))
  A1 := ↥(gluedLinesOverlap R a b ⊓ (invPolyPart R).prod (invPolyPart R))
  A01 := ↥(gluedLinesOverlap R a b)
  ρ0 := Subalgebra.inclusion inf_le_left
  ρ1 := Subalgebra.inclusion inf_le_left

variable {R}

def GluedCond (a b lam : Fin s → Rˣ) (f : R[T;T⁻¹] × R[T;T⁻¹]) : Prop :=
  ∀ i, levalUnit R (a i) f.1 = lam i * levalUnit R (b i) f.2

theorem GluedCond.add {a b lam : Fin s → Rˣ} {f g : R[T;T⁻¹] × R[T;T⁻¹]} (hf : GluedCond a b lam f)
    (hg : GluedCond a b lam g) : GluedCond a b lam (f + g) := fun i => by
  simp only [Prod.fst_add, Prod.snd_add, map_add, hf i, hg i, mul_add]

theorem GluedCond.zero (a b lam : Fin s → Rˣ) : GluedCond a b lam 0 := fun i => by simp

theorem GluedCond.mul {a b lam : Fin s → Rˣ} {g f : R[T;T⁻¹] × R[T;T⁻¹]}
    (hg : g ∈ gluedLinesOverlap R a b) (hf : GluedCond a b lam f) : GluedCond a b lam (g * f) := fun i => by
  simp only [Prod.fst_mul, Prod.snd_mul, map_mul, hg i, hf i]
  ring

variable (R)

def gluedLinesM01 (a b lam : Fin s → Rˣ) :
    Submodule ↥(gluedLinesOverlap R a b) (R[T;T⁻¹] × R[T;T⁻¹]) where
  carrier := {f | GluedCond a b lam f}
  add_mem' := fun hf hg => hf.add hg
  zero_mem' := GluedCond.zero a b lam
  smul_mem' := fun g _ hf => GluedCond.mul g.2 hf

def gluedLinesM0 (a b lam : Fin s → Rˣ) :
    Submodule ↥(gluedLinesOverlap R a b ⊓ (polyPart R).prod (polyPart R)) (R[T;T⁻¹] × R[T;T⁻¹]) where
  carrier := {f | GluedCond a b lam f ∧ f ∈ (polyPart R).prod (polyPart R)}
  add_mem' := fun hf hg => ⟨hf.1.add hg.1, Subalgebra.add_mem _ hf.2 hg.2⟩
  zero_mem' := ⟨GluedCond.zero a b lam, Subalgebra.zero_mem _⟩
  smul_mem' := fun g _ hf => ⟨GluedCond.mul g.2.1 hf.1, Subalgebra.mul_mem _ g.2.2 hf.2⟩

def gluedLinesM1 (a b lam : Fin s → Rˣ) (n m : ℤ) :
    Submodule ↥(gluedLinesOverlap R a b ⊓ (invPolyPart R).prod (invPolyPart R)) (R[T;T⁻¹] × R[T;T⁻¹]) where
  carrier := {f | GluedCond a b lam f ∧ f.1 * T (-n) ∈ invPolyPart R ∧ f.2 * T (-m) ∈ invPolyPart R}
  add_mem' := fun {f g} hf hg => ⟨hf.1.add hg.1, by
    rw [Prod.fst_add, add_mul]; exact Subalgebra.add_mem _ hf.2.1 hg.2.1, by
    rw [Prod.snd_add, add_mul]; exact Subalgebra.add_mem _ hf.2.2 hg.2.2⟩
  zero_mem' := ⟨GluedCond.zero a b lam, by
    rw [Prod.fst_zero, zero_mul]; exact Subalgebra.zero_mem _, by
    rw [Prod.snd_zero, zero_mul]; exact Subalgebra.zero_mem _⟩
  smul_mem' := fun g f hf => ⟨GluedCond.mul g.2.1 hf.1, by
    rw [Subalgebra.smul_def, smul_eq_mul, Prod.fst_mul, mul_assoc]
    exact Subalgebra.mul_mem _ (Subalgebra.mem_prod.mp g.2.2).1 hf.2.1, by
    rw [Subalgebra.smul_def, smul_eq_mul, Prod.snd_mul, mul_assoc]
    exact Subalgebra.mul_mem _ (Subalgebra.mem_prod.mp g.2.2).2 hf.2.2⟩

def gluedLinesSections (a b lam : Fin s → Rˣ) (n m : ℤ) : Sections.{u, u, u} (gluedLinesCover R a b) :=
  { M0 := ↥(gluedLinesM0 R a b lam)
    M1 := ↥(gluedLinesM1 R a b lam n m)
    M01 := ↥(gluedLinesM01 R a b lam)
    M0_addCommGroup := inferInstance
    M0_moduleA := Submodule.module _
    M0_module := Submodule.module' _
    M0_tower := Submodule.isScalarTower _
    M1_addCommGroup := inferInstance
    M1_moduleA := Submodule.module _
    M1_module := Submodule.module' _
    M1_tower := Submodule.isScalarTower _
    M01_addCommGroup := inferInstance
    M01_moduleA := Submodule.module _
    M01_module := Submodule.module' _
    M01_tower := Submodule.isScalarTower _
    r0 := { toFun := fun f => ⟨f.1, f.2.1⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    r1 := { toFun := fun f => ⟨f.1, f.2.1⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    r0_smul := fun _ _ => rfl
    r1_smul := fun _ _ => rfl }

end TwoChartCech

end
