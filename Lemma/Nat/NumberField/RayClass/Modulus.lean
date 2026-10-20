import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.RayClass.Modulus
open scoped nonZeroDivisors
open NumberField
open Modulus


/--
[mk_finitePart](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Modulus.lean)
-/
@[path]
private lemma mk_finitePart_eq
  [Field K] [NumberField K]
  {a : (Ideal (𝓞 K))⁰}
  {b : Finset (RealPlace K)} :
-- imply
  (⟨a, b⟩ : Modulus K).finitePart = a := by
-- proof
  apply NumberField.Modulus.mk_finitePart a b

/--
[mk_infinitePart](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Modulus.lean)
-/
@[path]
private lemma mk_infinitePart_eq
  [Field K] [NumberField K]
  {a : (Ideal (𝓞 K))⁰}
  {b : Finset (RealPlace K)} :
-- imply
  (⟨a, b⟩ : Modulus K).infinitePart = b := by
-- proof
  apply NumberField.Modulus.mk_infinitePart a b

/--
[one_finitePart](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Modulus.lean)
-/
@[path]
private lemma one_finitePart_eq
  [Field K] [NumberField K] :
-- imply
  (1 : Modulus K).finitePart = 1 := by
-- proof
  apply NumberField.Modulus.one_finitePart

/--
[one_infinitePart](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Modulus.lean)
-/
@[path]
private lemma one_infinitePart_eq
  [Field K] [NumberField K] :
-- imply
  (1 : Modulus K).infinitePart = ∅ := by
-- proof
  apply NumberField.Modulus.one_infinitePart

/--
[mul_finitePart](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Modulus.lean)
-/
@[path]
private lemma mul_finitePart_eq
  [Field K] [NumberField K]
  {m n : Modulus K} :
-- imply
  (m * n).finitePart = m.finitePart * n.finitePart := by
-- proof
  apply NumberField.Modulus.mul_finitePart m n

/--
[mul_infinitePart](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Modulus.lean)
-/
@[path]
private lemma mul_infinitePart_eq
  [Field K] [NumberField K]
  {m n : Modulus K} :
-- imply
  (m * n).infinitePart = m.infinitePart ∪ n.infinitePart := by
-- proof
  apply NumberField.Modulus.mul_infinitePart m n

/--
[dvd_unfold](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Modulus.lean)
-/
@[path]
private lemma dvd_unfold_eq
  [Field K] [NumberField K]
  {m n : Modulus K} :
-- imply
  (m ∣ n) ↔ (n.finitePart : Ideal (𝓞 K)) ≤ (m.finitePart : Ideal (𝓞 K)) ∧
    (↑m.infinitePart : Set (RealPlace K)) ⊆ ↑n.infinitePart := by
-- proof
  apply NumberField.Modulus.dvd_unfold m n

/--
[gcd_infinitePart](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Modulus.lean)
-/
@[path]
private lemma gcd_infinitePart_eq
  [Field K] [NumberField K]
  {m n : Modulus K} :
-- imply
  (gcd m n).infinitePart = m.infinitePart ∩ n.infinitePart := by
-- proof
  apply NumberField.Modulus.gcd_infinitePart m n

/--
[lcm_infinitePart](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Modulus.lean)
-/
@[path]
private lemma lcm_infinitePart_eq
  [Field K] [NumberField K]
  {m n : Modulus K} :
-- imply
  (lcm m n).infinitePart = m.infinitePart ∪ n.infinitePart := by
-- proof
  apply NumberField.Modulus.lcm_infinitePart m n

/--
[gcd_finitePart](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Modulus.lean)
-/
@[path]
private lemma gcd_finitePart_eq
  [Field K] [NumberField K]
  {m n : Modulus K} :
-- imply
  ((gcd m n).finitePart : Ideal (𝓞 K)) =
    (m.finitePart : Ideal (𝓞 K)) ⊔ (n.finitePart : Ideal (𝓞 K)) := by
-- proof
  apply NumberField.Modulus.gcd_finitePart m n

/--
[lcm_finitePart](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Modulus.lean)
-/
@[path]
private lemma lcm_finitePart_eq
  [Field K] [NumberField K]
  {m n : Modulus K} :
-- imply
  ((lcm m n).finitePart : Ideal (𝓞 K)) =
    (m.finitePart : Ideal (𝓞 K)) ⊓ (n.finitePart : Ideal (𝓞 K)) := by
-- proof
  apply NumberField.Modulus.lcm_finitePart m n

/--
[infinite_finitePart](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Modulus.lean)
-/
@[path]
private lemma infinite_finitePart_eq
  [Field K] [NumberField K]
  {v : RealPlace K} :
-- imply
  (infinite v).finitePart = 1 := by
-- proof
  apply NumberField.Modulus.infinite_finitePart v

/--
[infinite_infinitePart](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Modulus.lean)
-/
@[path]
private lemma infinite_infinitePart_eq
  [Field K] [NumberField K]
  {v : RealPlace K} :
-- imply
  (infinite v).infinitePart = {v} := by
-- proof
  apply NumberField.Modulus.infinite_infinitePart v

/--
[infinite_mul_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Modulus.lean)
-/
@[path]
private lemma infinite_mul_self_eq
  [Field K] [NumberField K]
  {v : RealPlace K} :
-- imply
  infinite v * infinite v = infinite v := by
-- proof
  apply NumberField.Modulus.infinite_mul_self v


-- created on 2026-10-20
