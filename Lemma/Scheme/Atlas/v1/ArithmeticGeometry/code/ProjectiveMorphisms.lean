import Mathlib
import sympy.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.ProjectiveMorphisms.Part6
open MvPolynomial ProjectiveRegularFunction ProjectiveRatMap ProjectiveThm1518
open scoped LinearAlgebra.Projectivization
open ProjectiveRegularFunction
open ProjectiveRatMap


namespace ProjectiveRegularFunction

/--
[HomogeneousRep.equivOn_trans](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveMorphisms.lean)
-/
@[path]
lemma HomogeneousRep.equivOn_trans
  {n : ℕ}
  {k : Type*}
  [Field k]
  {n' : ℕ}
  [Field k']
  {X : Set (ℙ k' (Fin (n' + 1) → k'))}
  {r₁ r₂ r₃ : HomogeneousRep n' k'}
-- given
  (h₁₂ : r₁.equivOn k' r₂ X)
  (h₂₃ : r₂.equivOn k' r₃ X)
  (hirr : ∀ (p q : MvPolynomial (Fin (n' + 1)) k'), (∀ P ∈ X, eval P.rep (p * q) = 0) → (∀ P ∈ X, eval P.rep p = 0) ∨ (∀ P ∈ X, eval P.rep q = 0))
  (h₂_nondeg : ¬(∀ P ∈ X, eval P.rep r₂.num = 0) ∨ ¬(∀ P ∈ X, eval P.rep r₂.den = 0)) :
-- imply
  r₁.equivOn k' r₃ X := by
-- proof
  have hnum_vanish : ∀ P ∈ X,
    eval P.rep (r₂.num * (r₁.num * r₃.den - r₃.num * r₁.den)) = 0 := by
    intro P hP
    have h1 := h₁₂ P hP
    have h2 := h₂₃ P hP
    simp only [map_sub, map_mul] at h1 h2 ⊢
    linear_combination eval P.rep r₁.num * h2 + eval P.rep r₃.num * h1
  have hden_vanish : ∀ P ∈ X,
    eval P.rep (r₂.den * (r₁.num * r₃.den - r₃.num * r₁.den)) = 0 := by
    intro P hP
    have h1 := h₁₂ P hP
    have h2 := h₂₃ P hP
    simp only [map_sub, map_mul] at h1 h2 ⊢
    linear_combination eval P.rep r₃.den * h1 + eval P.rep r₁.den * h2
  have hnum_or := hirr r₂.num (r₁.num * r₃.den - r₃.num * r₁.den) hnum_vanish
  have hden_or := hirr r₂.den (r₁.num * r₃.den - r₃.num * r₁.den) hden_vanish
  obtain hnum_zero | hdone := hnum_or
  · rcases hden_or with hden_zero | hdone
    ·
      obtain h | h := h₂_nondeg
      · exact absurd hnum_zero h
      · exact absurd hden_zero h
    · exact hdone
  · exact hdone

end ProjectiveRegularFunction

namespace ProjectiveRegularFunction

/--
[HomogeneousRep.evalAt_eq_of_equivOn](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveMorphisms.lean)
-/
@[path]
lemma HomogeneousRep.evalAt_eq_of_equivOn
  {n : ℕ}
  {k : Type*}
  [Field k]
  {r₁ r₂ : HomogeneousRep n k}
  {X : Set (ℙ k (Fin (n + 1) → k))}
  {P : ℙ k (Fin (n + 1) → k)}
-- given
  (hPX : P ∈ X)
  (hequiv : r₁.equivOn k r₂ X)
  (h₁ : r₁.isDefinedAt k P)
  (h₂ : r₂.isDefinedAt k P) :
-- imply
  r₁.evalAt k P = r₂.evalAt k P := by
-- proof
  unfold evalAt isDefinedAt at *
  have hP := hequiv P hPX
  simp only [map_sub, map_mul] at hP
  rw [div_eq_div_iff h₁ h₂]
  exact sub_eq_zero.mp hP

end ProjectiveRegularFunction

namespace ProjectiveRegularFunction

/--
[ProjectiveRatFun.mem_regularDomain_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveMorphisms.lean)
-/
@[path]
lemma ProjectiveRatFun.mem_regularDomain_iff
  {n : ℕ}
  {k : Type*}
  [Field k]
  {X : Set (ℙ k (Fin (n + 1) → k))}
  {r : ProjectiveRatFun n k X}
  {P : ℙ k (Fin (n + 1) → k)} :
-- imply
  P ∈ r.regularDomain k ↔ ∃ hP : P ∈ X, r.IsRegularAt k P hP := by
-- proof
  simp only [regularDomain, Set.mem_sep_iff, IsRegularAt]
  constructor
  · rintro ⟨hPX, rep, hrep, hdef⟩
    exact ⟨hPX, rep, hrep, hdef⟩
  · rintro ⟨hPX, rep, hrep, hdef⟩
    exact ⟨hPX, rep, hrep, hdef⟩

end ProjectiveRegularFunction

namespace ProjectiveRegularFunction

/--
[ProjectiveRatFun.evalAt_eq_rep](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveMorphisms.lean)
-/
@[path]
lemma ProjectiveRatFun.evalAt_eq_rep
  {n : ℕ}
  {k : Type*}
  [Field k]
  {X : Set (ℙ k (Fin (n + 1) → k))}
  {r : ProjectiveRatFun n k X}
  {P : ℙ k (Fin (n + 1) → k)}
  {rep : HomogeneousRep n k}
-- given
  (hP : P ∈ r.regularDomain k)
  (hrep : rep ∈ r.reps)
  (hdef : rep.isDefinedAt k P) :
-- imply
  r.evalAt k P hP = rep.evalAt k P := by
-- proof
  unfold evalAt
  apply HomogeneousRep.evalAt_eq_of_equivOn
  · exact hP.1
  · exact r.reps_equiv _ hP.2.choose_spec.1 _ hrep
  · exact hP.2.choose_spec.2
  · exact hdef
end ProjectiveRegularFunction
namespace ProjectiveRatMap
open MvPolynomial
open scoped LinearAlgebra.Projectivization
open ProjectiveRegularFunction


namespace ProjectiveRatMap

/--
[RationalMapTupleRep.equivOn_refl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveMorphisms.lean)
-/
@[path]
lemma RationalMapTupleRep.equivOn_refl
  {m n : ℕ}
  {k : Type*}
  [Field k]
  {X : Set (ℙ k (Fin (m + 1) → k))}
  {Y : Set (ℙ k (Fin (n + 1) → k))}
  {φ : RationalMapTupleRep m n k X Y} :
-- imply
  φ.equivOn k φ := by
-- proof
  intro i j P _
  simp only [map_sub, map_mul, sub_eq_zero]
  exact mul_comm _ _

end ProjectiveRatMap

namespace ProjectiveRatMap

/--
[RationalMapTupleRep.equivOn_symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveMorphisms.lean)
-/
@[path]
lemma RationalMapTupleRep.equivOn_symm
  {m n : ℕ}
  {k : Type*}
  [Field k]
  {X : Set (ℙ k (Fin (m + 1) → k))}
  {Y : Set (ℙ k (Fin (n + 1) → k))}
  {φ ψ : RationalMapTupleRep m n k X Y}
-- given
  (h : φ.equivOn k ψ) :
-- imply
  ψ.equivOn k φ := by
-- proof
  intro i j P hP
  have hval := h i j P hP
  simp only [map_sub, map_mul] at hval ⊢
  have h1 : eval P.rep (φ.polys i) * eval P.rep (ψ.polys j) =
    eval P.rep (φ.polys j) * eval P.rep (ψ.polys i) := sub_eq_zero.mp hval
  have h2 : eval P.rep (ψ.polys i) * eval P.rep (φ.polys j) =
    eval P.rep (ψ.polys j) * eval P.rep (φ.polys i) := by
    rwa [mul_comm (eval P.rep (ψ.polys i)), mul_comm (eval P.rep (ψ.polys j))]
  exact sub_eq_zero.mpr h2

end ProjectiveRatMap

namespace ProjectiveRatMap

/--
[RationalMapTupleRep.equivOn_trans](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveMorphisms.lean)
-/
@[path]
lemma RationalMapTupleRep.equivOn_trans
  {m n : ℕ}
  {k : Type*}
  [Field k]
  {X : Set (ℙ k (Fin (m + 1) → k))}
  {Y : Set (ℙ k (Fin (n + 1) → k))}
  {φ ψ χ : RationalMapTupleRep m n k X Y}
-- given
  (h₁ : φ.equivOn k ψ)
  (h₂ : ψ.equivOn k χ)
  (hirr : ∀ (p q : MvPolynomial (Fin (m + 1)) k), (∀ P ∈ X, eval P.rep (p * q) = 0) → (∀ P ∈ X, eval P.rep p = 0) ∨ (∀ P ∈ X, eval P.rep q = 0))
  (h₂_nondeg : ∃ a, ¬(∀ P ∈ X, eval P.rep (ψ.polys a) = 0)) :
-- imply
  φ.equivOn k χ := by
-- proof
  intro i j P hP
  obtain ⟨a, ha⟩ := h₂_nondeg
  have hkey : ∀ P ∈ X,
    eval P.rep (ψ.polys a * (φ.polys i * χ.polys j - φ.polys j * χ.polys i)) = 0 := by
    intro Q hQ
    have h1_ia := h₁ i a Q hQ
    have h1_ja := h₁ j a Q hQ
    have h2_ij := h₂ i j Q hQ
    simp only [map_sub, map_mul] at h1_ia h1_ja h2_ij ⊢
    linear_combination
      eval Q.rep (χ.polys j) * h1_ia -
      eval Q.rep (χ.polys i) * h1_ja +
      eval Q.rep (φ.polys a) * h2_ij
  have hor := hirr (ψ.polys a) (φ.polys i * χ.polys j - φ.polys j * χ.polys i) hkey
  obtain habs | hdone := hor
  · exact absurd habs ha
  · exact hdone P hP

end ProjectiveRatMap

namespace ProjectiveRatMap

/--
[ProjectiveRationalMap.mem_regularDomain_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveMorphisms.lean)
-/
@[path]
lemma ProjectiveRationalMap.mem_regularDomain_iff
  {m n : ℕ}
  {k : Type*}
  [Field k]
  {X : Set (ℙ k (Fin (m + 1) → k))}
  {Y : Set (ℙ k (Fin (n + 1) → k))}
  {φ : ProjectiveRationalMap m n k X Y}
  {P : ℙ k (Fin (m + 1) → k)} :
-- imply
  P ∈ φ.regularDomain k ↔ ∃ hP : P ∈ X, φ.IsRegularAt k P hP := by
-- proof
  simp only [regularDomain, Set.mem_sep_iff, IsRegularAt]
  constructor
  · rintro ⟨hPX, rep, hrep, hdef⟩
    exact ⟨hPX, rep, hrep, hdef⟩
  · rintro ⟨hPX, rep, hrep, hdef⟩
    exact ⟨hPX, rep, hrep, hdef⟩

end ProjectiveRatMap

namespace ProjectiveThm1518

variable {m n : ℕ} (k : Type*) [Field k]
/--
[eval_bind₁](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveMorphisms.lean)
-/
@[path]
lemma eval_bind₁ {k' : Type*} [CommSemiring k'] {σ τ : Type*}
  (v : τ → k') (f : σ → MvPolynomial τ k') (p : MvPolynomial σ k') :
  eval v (bind₁ f p) = eval (fun i => eval v (f i)) p := by
  have h := eval₂Hom_bind₁ (RingHom.id k') v f p
  simp only [eval, coe_eval₂Hom] at *
  convert h using 2

end ProjectiveThm1518

namespace ProjectiveThm1518

variable {m n : ℕ} (k : Type*) [Field k]
/--
[bind₁_isHomogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveMorphisms.lean)
-/
@[path]
lemma bind₁_isHomogeneous {k' : Type*} [CommSemiring k'] {σ τ : Type*}
  {p : MvPolynomial σ k'} {dp : ℕ} (hp : p.IsHomogeneous dp)
  {f : σ → MvPolynomial τ k'} {df : ℕ} (hf : ∀ i, (f i).IsHomogeneous df) :
  (bind₁ f p).IsHomogeneous (df * dp) := by
  rw [← aeval_eq_bind₁]; unfold aeval
  exact hp.eval₂ _ _ (fun r => isHomogeneous_C _ _) hf

end ProjectiveThm1518

namespace ProjectiveThm1518

/--
[eval_scale_homog'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveMorphisms.lean)
-/
@[path]
lemma eval_scale_homog'
  {m n : ℕ}
  {k : Type*}
  [Field k]
  [CommRing k']
  {p : MvPolynomial σ k'}
  {d : ℕ}
  {c : k'}
  {v : σ → k'}
-- given
  (hp : p.IsHomogeneous d) :
-- imply
  eval (fun i => c * v i) p = c ^ d * eval v p := by
-- proof
  rw [as_sum p, map_sum, map_sum, Finset.mul_sum]
  congr 1; ext s; simp only [eval_monomial]
  by_cases hcs : coeff s p = 0
  · simp [hcs]
  · simp_rw [mul_pow]; rw [Finsupp.prod_mul]
    have hprod : s.prod (fun _ e => c ^ e) = c ^ d := by
      unfold Finsupp.prod; rw [Finset.prod_pow_eq_pow_sum, ← hp hcs]
      congr 1; simp [Finsupp.weight, Finsupp.linearCombination, Finsupp.sum]
    rw [hprod]; ring

end ProjectiveThm1518

namespace ProjectiveThm1518

/--
[inducedPoly_homog](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveMorphisms.lean)
-/
@[path]
lemma inducedPoly_homog
  {m n : ℕ}
  {k : Type*}
  [Field k]
  {X : Set (ℙ k (Fin (m + 1) → k))}
  {Y : Set (ℙ k (Fin (n + 1) → k))}
  {θ : ProjectiveFunctionFieldHom m n k X Y}
  {i : Fin (n + 1)} :
-- imply
  (inducedPoly k θ i).IsHomogeneous (inducedCommonDeg k θ) := by
-- proof
  unfold inducedPoly inducedCommonDeg
  rw [← Finset.add_sum_erase Finset.univ (fun j => (inducedCoordRep k θ j).deg)
    (Finset.mem_univ i)]
  exact MvPolynomial.IsHomogeneous.mul (inducedCoordRep k θ i).num_homog
    (MvPolynomial.IsHomogeneous.prod _ _ _ (fun j _ => (inducedCoordRep k θ j).den_homog))
/-- The induced polynomials are not all vanishing on $X$: at some point $P \in X$ and some coordinate $i$, the induced polynomial is nonzero. -/
end ProjectiveThm1518
end


/--
[HomogeneousRep.equivOn_refl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveMorphisms.lean)
-/
@[path]
private lemma equivOn_refl_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {r : HomogeneousRep n k}
  {X : Set (ℙ k (Fin (n + 1) → k))} :
-- imply
  r.equivOn k r X := by
-- proof
  apply ProjectiveRegularFunction.HomogeneousRep.equivOn_refl k r X

/--
[HomogeneousRep.equivOn_symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveMorphisms.lean)
-/
@[path]
private lemma equivOn_symm_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {r₁ r₂ : HomogeneousRep n k}
  {X : Set (ℙ k (Fin (n + 1) → k))}
-- given
  (h : r₁.equivOn k r₂ X) :
-- imply
  r₂.equivOn k r₁ X := by
-- proof
  apply ProjectiveRegularFunction.HomogeneousRep.equivOn_symm k r₁ r₂ X h

/--
[eval_bind](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveMorphisms.lean)
-/
@[path]
private lemma eval_bind_eq
  {m n : ℕ}
  {k : Type*}
  [Field k]
  [CommSemiring k']
  {v : τ → k'}
  {f : σ → MvPolynomial τ k'}
  {p : MvPolynomial σ k'} :
-- imply
  eval v (bind₁ f p) = eval (fun i => eval v (f i)) p := by
-- proof
  apply ProjectiveThm1518.eval_bind k v f p

/--
[bind](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveMorphisms.lean)
-/
@[path]
private lemma bind_eq
  {m n : ℕ}
  {k : Type*}
  [Field k]
  [CommSemiring k']
  {p : MvPolynomial σ k'}
  {dp : ℕ}
  {f : σ → MvPolynomial τ k'}
  {df : ℕ}
-- given
  (hp : p.IsHomogeneous dp)
  (hf : ∀ i, (f i).IsHomogeneous df) :
-- imply
  (bind₁ f p).IsHomogeneous (df * dp) := by
-- proof
  apply ProjectiveThm1518.bind k hp hf


-- created on 2026-10-23
