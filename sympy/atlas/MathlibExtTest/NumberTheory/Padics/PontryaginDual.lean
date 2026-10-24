/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Padics/PontryaginDual.lean -/


import sympy.atlas.NumberTheory.Padics.PontryaginDual
import Lemma.Nat.Padics.PontryaginDual


namespace MetaMathlibExtTest

open MetaMathlibExt

private instance instDistribMulActionUnitPadicInt {p : ℕ} [Fact p.Prime] :
    DistribMulAction Unit ℤ_[p] where
  smul := fun _ a => a
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl
  smul_zero := fun _ => rfl
  smul_add := fun _ _ _ => rfl

private instance instSMulCommClassUnitPadicInt {p : ℕ} [Fact p.Prime] :
    SMulCommClass Unit ℤ_[p] ℤ_[p] where
  smul_comm := fun _ _ _ => rfl

example (p : ℕ) [Fact p.Prime] (z : ℤ_[p]) :
    padicQuotientMap p (algebraMap ℤ_[p] ℚ_[p] z) = 0 :=
  padicQuotientMap_algebraMap_eq_zero p z

example (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) :
    padicQuotientMap p x =
      Submodule.Quotient.mk (p := LinearMap.range (Algebra.linearMap ℤ_[p] ℚ_[p])) x :=
  rfl

example (p : ℕ) [Fact p.Prime] (A : Type*) [AddCommGroup A] [Module ℤ_[p] A]
    (φ ψ : PadicPontryaginDual p A) (h : ∀ a, φ a = ψ a) : φ = ψ :=
  PadicPontryaginDual_ext h

example (p : ℕ) [Fact p.Prime] (G A : Type*) [Group G] [AddCommGroup A] [Module ℤ_[p] A]
    [DistribMulAction G A] [SMulCommClass G ℤ_[p] A]
    (g : G) (φ : PadicPontryaginDual p A) (a : A) :
    (g • φ) a = φ (g⁻¹ • a) :=
  smul_apply p G A g φ a

example (p : ℕ) [Fact p.Prime] (G A : Type*) [Group G] [AddCommGroup A] [Module ℤ_[p] A]
    [DistribMulAction G A] [SMulCommClass G ℤ_[p] A]
    (φ : PadicPontryaginDual p A) : (1 : G) • φ = φ := by
  ext a
  change φ ((1 : G)⁻¹ • a) = φ a
  simp

example (p : ℕ) [Fact p.Prime] (G A : Type*) [Group G] [AddCommGroup A] [Module ℤ_[p] A]
    [DistribMulAction G A] [SMulCommClass G ℤ_[p] A]
    (g h : G) (φ : PadicPontryaginDual p A) : (g * h) • φ = g • h • φ := by
  ext a
  change φ ((g * h)⁻¹ • a) = φ (h⁻¹ • g⁻¹ • a)
  rw [mul_inv_rev, mul_smul]

example (p : ℕ) [Fact p.Prime] (φ : PadicPontryaginDual p ℤ_[p]) (a : ℤ_[p]) :
    ((() : Unit) • φ) a = φ a := by
  change φ ((() : Unit)⁻¹ • a) = φ a
  rfl

example (p : ℕ) [Fact p.Prime] (φ : PadicPontryaginDual p ℤ_[p]) :
    (() : Unit) • φ = φ := by
  apply PadicPontryaginDual_ext
  intro a
  change φ ((() : Unit)⁻¹ • a) = φ a
  rfl

example (p : ℕ) [Fact p.Prime] (φ : PadicPontryaginDual p ℤ_[p]) :
    ((() : Unit) * () : Unit) • φ = (() : Unit) • (() : Unit) • φ := by
  apply PadicPontryaginDual_ext
  intro a
  change φ ((() * () : Unit)⁻¹ • a) = φ ((() : Unit)⁻¹ • (() : Unit)⁻¹ • a)
  rfl

end MetaMathlibExtTest
