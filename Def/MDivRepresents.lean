import Mathlib
import Def.ModularCurve_ProlongationTuple
import Lemma.IncidenceSystem.Main
import Abbrev.MDivRepresents

set_option autoImplicit false

open AlgebraicCurve ModularCurve

namespace ModularCurve.PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

noncomputable def evalBar (N q : ℕ) (c : Option (Fin 2) → modularFunctionFieldBar (N * q))
    (H : MvPolynomial (Option (Fin 2)) A) : modularFunctionFieldBar (N * q) :=
  MvPolynomial.eval₂ ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).comp
    (algebraMap A (AlgebraicClosure ℚ))) c H

def IsFstTriple (v : Place k (modularFunctionFieldC k N)) (c : k) (z y₁ y₂ : modularFunctionFieldBar (N * q)) :
    Prop :=
  (z = ProlongationTuple.jFun N q ∧ y₁ = jNFun N q ∧ y₂ = jNQFun N q ∧
      v.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) c) = 1) ∨
    (z = jNFun N q ∧ y₁ = ProlongationTuple.jFun N q ∧ y₂ = jNQFun N q ∧
      v.ord (jNGeomGen k N - algebraMap k (modularFunctionFieldC k N) c) = 1)

def IsSndTriple (v : Place k (modularFunctionFieldC k N)) (c : k) (z y₁ y₂ : modularFunctionFieldBar (N * q)) :
    Prop :=
  (z = ProlongationTuple.jQFun N q ∧ y₁ = jNQFun N q ∧ y₂ = ProlongationTuple.jFun N q ∧
      v.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) c) = 1) ∨
    (z = jNQFun N q ∧ y₁ = ProlongationTuple.jQFun N q ∧ y₂ = ProlongationTuple.jFun N q ∧
      v.ord (jNGeomGen k N - algebraMap k (modularFunctionFieldC k N) c) = 1)

def MDivRepresents (P : PlaceSpecialization A q N data hKr k red hα hβ)
    {d₁ d₂ : ℕ}
    (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (m' : ℕ) (h : Fin ((d₁ + d₂) * m' + 1) → modularFunctionFieldBar (N * q))
    (D : IncidenceSystem.Data (d₁ + d₂) 2 m' A) : Prop :=
  (∀ i : Fin (d₁ + d₂),
    ∃ (z y₁ y₂ : modularFunctionFieldBar (N * q)) (τ : A),

      Sum.elim (fun i₁ => IsFstTriple (q := q) (P.reduceFst (Q₁ i₁)) (red (D.u₀ i)) z y₁ y₂)
          (fun i₂ => IsSndTriple (q := q) (P.reduceSnd (Q₂ i₂)) (red (D.u₀ i)) z y₁ y₂) (finSumFinEquiv.symm i) ∧

      (∀ j : Fin 2, evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (D.G i j) = 0) ∧
      (some 1 : Option (Fin 2)) ∉ (D.G i 0).vars ∧

      0 < (Sum.elim Q₁ Q₂ (finSumFinEquiv.symm i)).ord
            (z - algebraMap (AlgebraicClosure ℚ) _ (D.u₀ i : AlgebraicClosure ℚ)) ∧
      (∀ j : Fin 2, 0 < (Sum.elim Q₁ Q₂ (finSumFinEquiv.symm i)).ord
            (![y₁, y₂] j - algebraMap (AlgebraicClosure ℚ) _ (D.w₀ i j 0 : AlgebraicClosure ℚ))) ∧
      0 < (Sum.elim Q₁' Q₂' (finSumFinEquiv.symm i)).ord
            (z - algebraMap (AlgebraicClosure ℚ) _ (τ : AlgebraicClosure ℚ)) ∧

      (∀ kk : Option (Fin ((d₁ + d₂) * m')),
        evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (D.p kk i) =
          Option.elim kk 1 (fun kk => h kk.succ) *
            (z - algebraMap (AlgebraicClosure ℚ) _ (D.u₀ i : AlgebraicClosure ℚ)) ^ m' *
            (z - algebraMap (AlgebraicClosure ℚ) _ (τ : AlgebraicClosure ℚ)) *
            evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (D.s kk i)) ∧
      D.p none i = (MvPolynomial.X none - MvPolynomial.C (D.u₀ i)) ^ m' *
        (MvPolynomial.X none - MvPolynomial.C τ) ∧
      D.s none i = 1 ∧
      D.σ₀ none i = Pi.single 0 1 ∧

      (∀ kk : Option (Fin ((d₁ + d₂) * m')), red (D.sVal D.centre kk i) ≠ 0) ∧

      (∀ j : Fin 2, red (D.dG D.centre i j) ≠ 0)) ∧

  (∀ v : IncidenceSystem.Var (d₁ + d₂) 2 m',
    MvPolynomial.eval D.centre (D.system v) ∈ IsLocalRing.maximalIdeal A)

end ModularCurve.PlaceSpecialization
