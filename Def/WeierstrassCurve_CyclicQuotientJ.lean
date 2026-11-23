import Mathlib
import Theorem.WeierstrassCurve.Velu
import Theorem.WeierstrassCurve.VeluOrderTwo
import Lemma.WeierstrassCurve.VeluPointMap2
import Theorem.WeierstrassCurve.OddOrderSummingSet
import Abbrev.WeierstrassCurve_CyclicQuotientJ

set_option autoImplicit false

noncomputable section

namespace WeierstrassCurve

section XData

variable {R : Type*} [CommRing R] (V : WeierstrassCurve R)

def xVeluT (x : R) : R := 6 * x ^ 2 + V.b₂ * x + V.b₄

def xVeluU (x : R) : R := 4 * x ^ 3 + V.b₂ * x ^ 2 + 2 * V.b₄ * x + V.b₆

def xVeluW (x : R) : R := V.xVeluU x + x * V.xVeluT x

end XData

section Field

variable {L : Type*} [Field L]

def absSum (X : Set L) (g : L → L) : L :=
  haveI := Classical.dec X.Finite
  if X.Finite then ∑ᶠ x ∈ X, g x else 0

def xVeluCurve (V : WeierstrassCurve L) (X : Set L) : WeierstrassCurve L where
  a₁ := V.a₁
  a₂ := V.a₂
  a₃ := V.a₃
  a₄ := V.a₄ - 5 * absSum X V.xVeluT
  a₆ := V.a₆ - V.b₂ * absSum X V.xVeluT - 7 * absSum X V.xVeluW

def xVeluX (V : WeierstrassCurve L) (X : Set L) (x : L) : L :=
  x + absSum X fun x₀ => V.xVeluT x₀ / (x - x₀) + V.xVeluU x₀ / (x - x₀) ^ 2

def twoTorsionY (V : WeierstrassCurve L) (x₀ : L) : L := -(V.a₁ * x₀ + V.a₃) / 2

def xVeluG (V : WeierstrassCurve L) (x₀ : L) : L := V.veluGx x₀ (V.twoTorsionY x₀)

def twoVeluCurve (V : WeierstrassCurve L) (X : Set L) : WeierstrassCurve L where
  a₁ := V.a₁
  a₂ := V.a₂
  a₃ := V.a₃
  a₄ := V.a₄ - 5 * absSum X V.xVeluG
  a₆ := V.a₆ - V.b₂ * absSum X V.xVeluG - 7 * absSum X fun x => x * V.xVeluG x

def twoVeluX (V : WeierstrassCurve L) (X : Set L) (x : L) : L :=
  x + absSum X fun x₀ => V.xVeluG x₀ / (x - x₀)

variable [DecidableEq L]

def kernelXSet (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (ℓ : ℕ) : Set L :=
  (fun P => P.coordsOrZero.1) '' {P | P ∈ H ∧ P ≠ 0 ∧ ℓ • P = 0}

def coKernelXSet (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (ℓ : ℕ) : Set L :=
  (fun P => P.coordsOrZero.1) '' {P | P ∈ H ∧ ℓ • P ≠ 0}

def stepCurve (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (ℓ : ℕ) :
    WeierstrassCurve L :=
  if ℓ = 2 then V.twoVeluCurve (V.kernelXSet H 2) else V.xVeluCurve (V.kernelXSet H ℓ)

def stepX (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (ℓ : ℕ) (x : L) : L :=
  if ℓ = 2 then V.twoVeluX (V.kernelXSet H 2) x else V.xVeluX (V.kernelXSet H ℓ) x

def subgroupOfX (V' : WeierstrassCurve L) (Y : Set L) : AddSubgroup V'.toAffine.Point :=
  AddSubgroup.closure {P | P ≠ 0 ∧ P.coordsOrZero.1 ∈ Y}

def stepSubgroup (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (ℓ : ℕ) :
    AddSubgroup (V.stepCurve H ℓ).toAffine.Point :=
  subgroupOfX (V.stepCurve H ℓ) (V.stepX H ℓ '' V.coKernelXSet H ℓ)

def cqjStep (s : CQJState L) : CQJState L :=
  ⟨⟨s.1.1.stepCurve s.1.2 s.2.minFac, s.1.1.stepSubgroup s.1.2 s.2.minFac⟩, s.2 / s.2.minFac⟩

def cqjIterate (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (N : ℕ) : CQJState L :=
  cqjStep^[N.primeFactorsList.length] ⟨⟨V, H⟩, N⟩

def cyclicQuotientCurve (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (N : ℕ) :
    WeierstrassCurve L :=
  (V.cqjIterate H N).1.1

def cyclicQuotientJ (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (N : ℕ) : L :=
  (V.cyclicQuotientCurve H N).c₄ ^ 3 / (V.cyclicQuotientCurve H N).Δ

end Field

end WeierstrassCurve

end
