import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.ArithmeticGeometry.code.Theorem1324
open MvPolynomial Finsupp Thm1324
open scoped LinearAlgebra.Projectivization
open ProjectiveVarietyDef ProjectiveVanishingIdeal AffineParts


namespace Thm1324

/--
[eval_dehomogenize_eq_general](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Theorem1324.lean)
-/
@[path]
lemma eval_dehomogenize_eq_general
  {n : ℕ}
  {k : Type*}
  [Field k]
  {i : Fin (n + 1)}
  {g : MvPolynomial (Fin (n + 1)) k}
  {P : Fin n → k} :
-- imply
  eval P (AffineParts.dehomogenize k i g) = eval (i.insertNth (1 : k) P) g := by
-- proof
  have hcomp : (eval P).comp (AffineParts.dehomogenize k i) =
    eval (i.insertNth (1 : k) P) := by
    apply ringHom_ext
    · intro a; simp [AffineParts.dehomogenize]
    · intro j
      simp only [RingHom.comp_apply, AffineParts.dehomogenize, eval₂Hom_X']
      by_cases hj : j = i
      · subst hj; simp [Fin.insertNth_apply_same]
      · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hj; simp
  rw [← RingHom.comp_apply, hcomp]

end Thm1324

namespace Thm1324

/--
[eval_dehomogenize_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Theorem1324.lean)
-/
@[path]
lemma eval_dehomogenize_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {g : MvPolynomial (Fin (n + 1)) k}
  {P : Fin n → k} :
-- imply
  eval P (AffineParts.dehomogenize k (0 : Fin (n + 1)) g) = eval ((0 : Fin (n + 1)).insertNth (1 : k) P) g :=
-- proof
  eval_dehomogenize_eq_general k 0 g P

end Thm1324

namespace Thm1324

/--
[dehomogenize_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Theorem1324.lean)
-/
@[path]
lemma dehomogenize_surjective
  {n : ℕ}
  {k : Type*}
  [Field k]
  {i : Fin (n + 1)} :
-- imply
  Function.Surjective (AffineParts.dehomogenize k i) :=
-- proof
  Theorem1324.dehomogenize_surjective k i

end Thm1324

namespace Thm1324

/--
[dehomogenizedIdeal_isPrime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Theorem1324.lean)
-/
@[path]
lemma dehomogenizedIdeal_isPrime
  {n : ℕ}
  {k : Type*}
  [Field k]
  {I : Ideal (MvPolynomial (Fin (n + 1)) k)}
  [hI : I.IsPrime]
  {i : Fin (n + 1)}
-- given
  (hker : RingHom.ker (AffineParts.dehomogenize k i) ≤ I) :
-- imply
  (I.map (AffineParts.dehomogenize k i)).IsPrime :=
-- proof
  Ideal.map_isPrime_of_surjective (dehomogenize_surjective k i) hker

end Thm1324

namespace Thm1324

/--
[projective_closure_of_affinePart_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Theorem1324.lean)
-/
@[path]
lemma projective_closure_of_affinePart_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {I : Ideal (MvPolynomial (Fin (n + 1)) k)}
  {i : Fin (n + 1)} :
-- imply
  {P : Fin n → k | ∀ f ∈ I, eval (i.insertNth (1 : k) P) f = 0} = {P : Fin n → k | ∀ h ∈ I.map (AffineParts.dehomogenize k i), eval P h = 0} := by
-- proof
  ext P
  simp only [Set.mem_setOf_eq]
  constructor
  ·
    intro hP h hh
    have : I.map (AffineParts.dehomogenize k i) ≤ RingHom.ker (eval P) := by
      rw [Ideal.map_le_iff_le_comap]
      intro f hf
      simp only [Ideal.mem_comap, RingHom.mem_ker]
      rw [eval_dehomogenize_eq_general]
      exact hP f hf
    exact this hh
  ·
    intro hP f hf
    rw [← eval_dehomogenize_eq_general k i f P]
    exact hP _ (Ideal.mem_map_of_mem _ hf)

end Thm1324

namespace Thm1324

/--
[theorem_13_24](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Theorem1324.lean)
-/
@[path]
lemma theorem_13_24
  {n : ℕ}
  {k : Type*}
  [Field k]
  {I : Ideal (MvPolynomial (Fin (n + 1)) k)}
  [hI : I.IsPrime]
  {i : Fin (n + 1)}
-- given
  (hker : RingHom.ker (AffineParts.dehomogenize k i) ≤ I) :
-- imply
  (I.map (AffineParts.dehomogenize k i)).IsPrime ∧ ({P : Fin n → k | ∀ f ∈ I, eval (i.insertNth (1 : k) P) f = 0} = {P : Fin n → k | ∀ h ∈ I.map (AffineParts.dehomogenize k i), eval P h = 0}) ∧ ({P : Fin n → k | ∀ f ∈ I, eval ((0 : Fin (n + 1)).insertNth (1 : k) P) f = 0} = {P : Fin n → k | ∀ g ∈ ProjectiveClosure.homogenizeIdeal (I.map (AffineParts.dehomogenize k 0)), eval ((0 : Fin (n + 1)).insertNth (1 : k) P) g = 0}) :=
-- proof
  ⟨dehomogenizedIdeal_isPrime k I i hker,
    projective_closure_of_affinePart_eq k I i,
    Theorem1324.projective_closure_of_affinePart_eq k I⟩
end Thm1324
noncomputable section
set_option maxHeartbeats 400000
open MvPolynomial Finsupp
open scoped LinearAlgebra.Projectivization
namespace Thm1324Geometric
variable {n : ℕ} (k : Type*) [Field k]
open ProjectiveVarietyDef ProjectiveVanishingIdeal AffineParts
/-- The projective vanishing ideal $I(V)$ of an irreducible (projective) variety $V$ is prime:
if $fg \in I(V)$ then $f \in I(V)$ or $g \in I(V)$, reflecting the irreducibility of $V$. -/
end Thm1324Geometric
end



-- created on 2026-10-23
