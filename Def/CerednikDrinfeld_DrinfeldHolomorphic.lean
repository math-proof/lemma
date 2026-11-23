import Theorem.Matrix.DrinfeldUpperHalfPlane
import Def.CerednikDrinfeld_MumfordQuotient
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Algebra.Polynomial.Eval.Defs
import Structure.CerednikDrinfeld_DrinfeldHolomorphic
import Abbrev.CerednikDrinfeld_DrinfeldHolomorphic
import Notation.CerednikDrinfeld_DrinfeldHolomorphic

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups
open Filter CerednikDrinfeld.Omega CerednikDrinfeld.Mumford

namespace CerednikDrinfeld.Omega

variable (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]


variable {K₀ K} (ϖ : PseudoUniformizer K₀ K)

def affinoid (n : ℕ) : Set K :=
  {z | Valued.v z ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n ∧
    ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
      (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n ≤ Valued.v (z - algebraMap K₀ K a)}

def IsExhausted : Prop := ∀ z ∈ upperHalfPlane K₀ K, ∃ n, z ∈ affinoid ϖ n


namespace RatPair

def IsPoleFreeOn (S : Set K) (r : RatPair K) : Prop := ∀ z ∈ S, r.den.eval z ≠ 0

def evalAt (r : RatPair K) (z : K) : K := r.num.eval z / r.den.eval z

def const (c : K) : RatPair K := ⟨Polynomial.C c, 1⟩

def add (p q : RatPair K) : RatPair K := ⟨p.num * q.den + q.num * p.den, p.den * q.den⟩

def mul (p q : RatPair K) : RatPair K := ⟨p.num * q.num, p.den * q.den⟩

def neg (p : RatPair K) : RatPair K := ⟨-p.num, p.den⟩

def homog (a b c d : K) (D : ℕ) (P : Polynomial K) : Polynomial K :=
  ∑ i ∈ Finset.range (D + 1), Polynomial.C (P.coeff i) * (Polynomial.C a * Polynomial.X + Polynomial.C b) ^ i *
    (Polynomial.C c * Polynomial.X + Polynomial.C d) ^ (D - i)

def pullback (g : GL (Fin 2) K₀) (r : RatPair K) : RatPair K :=
  ⟨homog (algebraMap K₀ K (g 0 0)) (algebraMap K₀ K (g 0 1)) (algebraMap K₀ K (g 1 0)) (algebraMap K₀ K (g 1 1))
      (max r.num.natDegree r.den.natDegree) r.num,
   homog (algebraMap K₀ K (g 0 0)) (algebraMap K₀ K (g 0 1)) (algebraMap K₀ K (g 1 0)) (algebraMap K₀ K (g 1 1))
      (max r.num.natDegree r.den.natDegree) r.den⟩

def map (s : K ≃+* K) (r : RatPair K) : RatPair K := ⟨r.num.map (s : K →+* K), r.den.map (s : K →+* K)⟩

end RatPair

section Hol

variable (K)

def IsHolOn (S : Set K) (f : ↥S → K) : Prop :=
  ∃ r : ℕ → RatPair K, (∀ k, (r k).IsPoleFreeOn S) ∧
    (∃ b : K, ∀ k (z : ↥S), Valued.v ((r k).evalAt z) ≤ Valued.v b) ∧
    TendstoUniformly (fun k (z : ↥S) => (r k).evalAt z) f atTop

variable {K}

variable (K) in

def holOn (S : Set K) : Subring (↥S → K) where
  carrier := {f | IsHolOn K S f}
  mul_mem' hf hg := hf.mul hg
  one_mem' := IsHolOn.one S
  add_mem' hf hg := hf.add hg
  zero_mem' := IsHolOn.zero S
  neg_mem' hf := hf.neg

end Hol

def restrictAffinoid (n : ℕ) (f : ↥(upperHalfPlane K₀ K) → K) : ↥(affinoid ϖ n) → K :=
  f ∘ Set.inclusion (affinoid_subset_upperHalfPlane ϖ n)

def holRing : Subring (↥(upperHalfPlane K₀ K) → K) where
  carrier := {f | ∀ n, IsHolOn K (affinoid ϖ n) (restrictAffinoid ϖ n f)}
  mul_mem' hf hg := fun n => (hf n).mul (hg n)
  one_mem' := fun _ => IsHolOn.one _
  add_mem' hf hg := fun n => (hf n).add (hg n)
  zero_mem' := fun _ => IsHolOn.zero _
  neg_mem' hf := fun n => (hf n).neg

def holSubalgebra : Subalgebra K (↥(upperHalfPlane K₀ K) → K) :=
  { holRing ϖ with algebraMap_mem' := fun c => const_mem_holRing ϖ c }

section Actions

variable [DecidableEq K]

def precomp (g : PGL(2, K₀)) (f : ↥(upperHalfPlane K₀ K) → K) : ↥(upperHalfPlane K₀ K) → K := fun z => f (g⁻¹ • z)

section Stab

open scoped CerednikDrinfeld_DrinfeldHolomorphic

omit [DecidableEq K] in
end Stab

namespace IsometricAut

omit [DecidableEq K] in
def funMap (s : IsometricAut K₀ K) : (↥(upperHalfPlane K₀ K) → K) ≃+* (↥(upperHalfPlane K₀ K) → K) where
  toFun f := fun z => s.toRingEquiv (f ⟨s.toRingEquiv.symm z, (s⁻¹).mapsTo_upperHalfPlane z.2⟩)
  invFun f := fun z => s.toRingEquiv.symm (f ⟨s.toRingEquiv z, s.mapsTo_upperHalfPlane z.2⟩)
  left_inv f := funext fun z => by simp
  right_inv f := funext fun z => by simp
  map_mul' f f' := funext fun z => map_mul s.toRingEquiv _ _
  map_add' f f' := funext fun z => map_add s.toRingEquiv _ _

omit [DecidableEq K] in
def coeffMap (s : IsometricAut K₀ K) : ↥(holRing ϖ) ≃+* ↥(holRing ϖ) where
  toFun f := ⟨s.funMap f, s.funMap_mem_holRing ϖ f.2⟩
  invFun f := ⟨(s⁻¹).funMap f, (s⁻¹).funMap_mem_holRing ϖ f.2⟩
  left_inv f := Subtype.ext (funext fun z => by simp [funMap])
  right_inv f := Subtype.ext (funext fun z => by simp [funMap])
  map_mul' f f' := Subtype.ext (map_mul s.funMap _ _)
  map_add' f f' := Subtype.ext (map_add s.funMap _ _)

omit [DecidableEq K] in
def toAmbient (s : IsometricAut K₀ K) : Mumford.AmbientSemilinearAut K PGL(2, K₀) ↥(holRing ϖ) where
  base := s.toRingEquiv
  map := s.coeffMap ϖ
  map_algebraMap := s.coeffMap_algebraMap ϖ
  map_smul := fun g f => s.coeffMap_smul ϖ g f

end IsometricAut

end Actions

section Hom

variable [DecidableEq K]

def IsometricAut.toAmbientHom : IsometricAut K₀ K →* Mumford.AmbientSemilinearAut K PGL(2, K₀) ↥(holRing ϖ) where
  toFun s := s.toAmbient ϖ
  map_one' := Mumford.AmbientSemilinearAut.ext rfl
    (RingEquiv.ext fun f => Subtype.ext (funext fun _ => congrArg (f : ↥(upperHalfPlane K₀ K) → K) (Subtype.ext rfl)))
  map_mul' _ _ := Mumford.AmbientSemilinearAut.ext rfl
    (RingEquiv.ext fun _ => Subtype.ext (funext fun _ => rfl))

end Hom

section Glue

variable [DecidableEq K] {G : Type} [Group G] (ρ : G →* PGL(2, K₀))

set_option linter.unusedVariables false in

def HolRingOf (ρ : G →* PGL(2, K₀)) : Type := ↥(holRing ϖ)

def toAmbientOf (s : IsometricAut K₀ K) : Mumford.AmbientSemilinearAut K G (HolRingOf ϖ ρ) where
  base := s.toRingEquiv
  map := s.coeffMap ϖ
  map_algebraMap := s.coeffMap_algebraMap ϖ
  map_smul := fun g f => s.coeffMap_smul ϖ (ρ g) f

def toAmbientOfHom : IsometricAut K₀ K →* Mumford.AmbientSemilinearAut K G (HolRingOf ϖ ρ) where
  toFun := toAmbientOf ϖ ρ
  map_one' := Mumford.AmbientSemilinearAut.ext rfl
    (RingEquiv.ext fun f => Subtype.ext (funext fun _ =>
      congrArg ((show ↥(holRing ϖ) from f) : ↥(upperHalfPlane K₀ K) → K) (Subtype.ext rfl)))
  map_mul' _ _ := Mumford.AmbientSemilinearAut.ext rfl
    (RingEquiv.ext fun _ => Subtype.ext (funext fun _ => rfl))

end Glue

abbrev merField : Type := FractionRing ↥(holRing ϖ)

end CerednikDrinfeld.Omega

end
