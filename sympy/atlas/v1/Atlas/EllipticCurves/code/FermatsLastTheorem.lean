/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FermatsLastTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import sympy.atlas.v1.Atlas.EllipticCurves.code.Isogenies
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Isogenies

noncomputable section GaloisRepInfra

open Matrix CongruenceSubgroup

/-- The algebraic closure of `ℚ` inside `ℂ`, viewed as an intermediate field. This
provides a concrete model of `ℚ̄` sitting inside `ℂ`. -/
abbrev Qbar : IntermediateField ℚ ℂ := algebraicClosure ℚ ℂ

/-- The absolute Galois group of `ℚ`, realized as the group of `ℚ`-algebra
automorphisms of `Qbar`. -/
abbrev AbsGaloisGroupQ := ↥Qbar ≃ₐ[ℚ] ↥Qbar

/-- A mod-`ℓ` Galois representation is a group homomorphism from the absolute Galois
group of `ℚ` to `GL₂(ℤ/ℓℤ)`. -/
abbrev GaloisRepMod (ℓ : ℕ) := AbsGaloisGroupQ →* GL (Fin 2) (ZMod ℓ)

/-- A specific element of the absolute Galois group of `ℚ` realizing complex
conjugation on `Qbar ⊆ ℂ`. -/
def GaloisRepMod.IsIrreducible {ℓ : ℕ} (ρ : GaloisRepMod ℓ) : Prop :=
  ∀ (v : Fin 2 → ZMod ℓ), v ≠ 0 →
    ¬∀ (g : AbsGaloisGroupQ),
      ∃ (c : ZMod ℓ), (↑(ρ g) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) *ᵥ v = c • v

/-- An element of the absolute Galois group realizing a Frobenius at the prime `p`. -/
end GaloisRepInfra

noncomputable section

namespace FLT

/-- An elliptic curve over `ℚ`: a Weierstrass curve in affine form together with a
proof that it satisfies the elliptic (nonsingular) condition. -/
abbrev EllipticCurveOverQ := { E : WeierstrassCurve.Affine ℚ // E.IsElliptic }

open UniqueFactorizationMonoid

/-- The minimal discriminant of an elliptic curve over `ℚ`: the discriminant of a
global minimal Weierstrass model. -/
def IsSemistable (E : EllipticCurveOverQ) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R ℚ] [IsFractionRing R ℚ],
    ¬ (E.val.minimal R).HasAdditiveReduction R

/-- An elliptic curve over `ℚ` is semistable iff its conductor is squarefree. -/
structure Weight2Newform (N : ℕ) where
  coeff : ℕ → ℤ
  coeff_one : coeff 1 = 1
  coeff_mult : ∀ m n : ℕ, Nat.Coprime m n → coeff (m * n) = coeff m * coeff n
  coeff_prime_power : ∀ (p : ℕ) (r : ℕ), Nat.Prime p → ¬(p ∣ N) → r ≥ 1 →
    coeff (p ^ (r + 1)) = coeff p * coeff (p ^ r) - (p : ℤ) * coeff (p ^ (r - 1))

/-- The mod-`ℓ` representation of `E/ℚ` is modular of a prescribed weight and level:
there is a weight-`2` newform of the given level matching `tr ρ(Frob_p)` at primes
`p ∤ ℓ · level`. -/
instance : Fact (Nat.Prime 3) := ⟨by decide⟩
/-- `5` is a prime number. Provided as a `Fact` for use as a typeclass parameter. -/
instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The mod-`ℓ` representations of two elliptic curves `E, E'` over `ℚ` are
isomorphic (at the level of traces): for every `g` in the absolute Galois group,
`tr ρ_E(g) = tr ρ_{E'}(g)`. -/
end FLT

end

noncomputable section

namespace EllipticCurve

/-- Convenience abbreviation for `FLT.EllipticCurveOverQ`, the type of elliptic
curves over `ℚ`. -/
abbrev OverQ := FLT.EllipticCurveOverQ

/-- The conductor of an elliptic curve over `ℚ`, re-exported from the `FLT` namespace. -/
def IsSemistable (E : FLT.EllipticCurveOverQ) : Prop := FLT.IsSemistable E

/-- Re-export: semistability is equivalent to the conductor being squarefree. -/
end EllipticCurve

end

noncomputable section

/-- Serre's modularity conjecture (now a theorem of Khare–Wintenberger): every odd,
irreducible mod-`ℓ` Galois representation of `Gal(ℚ̄/ℚ)` arises from a modular
form. -/
end
