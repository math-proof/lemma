import Mathlib
import Initialize.Tactic.Attr.Basic
open Ideal Polynomial UniqueFactorizationMonoid KummerDedekind NumberField


namespace DedekindKummer

/--
[inertiaDeg_eq_natDegree_lift](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/KummerInertiaDeg.lean)
-/
@[path]
lemma inertiaDeg_eq_natDegree_lift
  [Field K]
  [NumberField K]
  {p : ℕ} [Fact (Nat.Prime p)]
  {θ : 𝓞 K}
  {Q : ℤ[X]}
-- given
  (hp : ¬ p ∣ RingOfIntegers.exponent θ)
  (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ RingOfIntegers.monicFactorsMod θ p) :
-- imply
  inertiaDeg ((Ideal.primesOverSpanEquivMonicFactorsMod hp).symm
      ⟨Q.map (Int.castRingHom (ZMod p)), hQ⟩ : Ideal (𝓞 K)) ℤ =
    (Q.map (Int.castRingHom (ZMod p))).natDegree :=
-- proof
  NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply hp hQ

end DedekindKummer

namespace DedekindKummer

/--
[ramificationIdx_eq_multiplicity_lift](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/KummerInertiaDeg.lean)
-/
@[path]
lemma ramificationIdx_eq_multiplicity_lift
  [Field K]
  [NumberField K]
  {p : ℕ} [Fact (Nat.Prime p)]
  {θ : 𝓞 K}
  {Q : ℤ[X]}
-- given
  (hp : ¬ p ∣ RingOfIntegers.exponent θ)
  (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ RingOfIntegers.monicFactorsMod θ p) :
-- imply
  ramificationIdx ((Ideal.primesOverSpanEquivMonicFactorsMod hp).symm
      ⟨Q.map (Int.castRingHom (ZMod p)), hQ⟩ : Ideal (𝓞 K)) ℤ =
    multiplicity (Q.map (Int.castRingHom (ZMod p)))
      ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) :=
-- proof
  NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply hp hQ

end DedekindKummer

namespace DedekindKummer

/--
[prime_eq_span_pair](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/KummerInertiaDeg.lean)
-/
@[path]
lemma prime_eq_span_pair
  [Field K]
  [NumberField K]
  {p : ℕ} [Fact (Nat.Prime p)]
  {θ : 𝓞 K}
  {Q : ℤ[X]}
-- given
  (hp : ¬ p ∣ RingOfIntegers.exponent θ)
  (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ RingOfIntegers.monicFactorsMod θ p) :
-- imply
  ((Ideal.primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q.map (Int.castRingHom (ZMod p)), hQ⟩ : Ideal (𝓞 K)) = span {(p : 𝓞 K), aeval θ Q} :=
-- proof
  NumberField.Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span hp hQ

end DedekindKummer

namespace DedekindKummer

/--
[kummer_inertiaDeg_ramificationIdx_prime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/KummerInertiaDeg.lean)
-/
@[path]
lemma kummer_inertiaDeg_ramificationIdx_prime
  [Field K]
  [NumberField K]
  {p : ℕ} [Fact (Nat.Prime p)]
  {θ : 𝓞 K}
  {Q : ℤ[X]}
-- given
  (hp : ¬ p ∣ RingOfIntegers.exponent θ)
  (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ RingOfIntegers.monicFactorsMod θ p) :
-- imply
  inertiaDeg ((Ideal.primesOverSpanEquivMonicFactorsMod hp).symm
      ⟨Q.map (Int.castRingHom (ZMod p)), hQ⟩ : Ideal (𝓞 K)) ℤ =
    (Q.map (Int.castRingHom (ZMod p))).natDegree ∧
      ramificationIdx ((Ideal.primesOverSpanEquivMonicFactorsMod hp).symm
        ⟨Q.map (Int.castRingHom (ZMod p)), hQ⟩ : Ideal (𝓞 K)) ℤ =
    multiplicity (Q.map (Int.castRingHom (ZMod p)))
      ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) ∧
      ((Ideal.primesOverSpanEquivMonicFactorsMod hp).symm
        ⟨Q.map (Int.castRingHom (ZMod p)), hQ⟩ : Ideal (𝓞 K)) =
    span {(p : 𝓞 K), aeval θ Q} :=
-- proof
  ⟨inertiaDeg_eq_natDegree_lift hp hQ,
    ramificationIdx_eq_multiplicity_lift hp hQ,
    prime_eq_span_pair hp hQ⟩

end DedekindKummer


-- created on 2026-10-23
-- updated on 2026-10-29
