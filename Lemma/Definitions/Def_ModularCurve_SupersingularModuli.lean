import Lemma.Definitions.Def_ModularCurve_ModuliPoint

set_option autoImplicit false

namespace ModularCurve

def ssJSet (p : ℕ) (K : Type*) [Field K] [DecidableEq K] : Set K :=
  {j | ∀ (W : WeierstrassCurve K) [W.IsElliptic], W.j = j →
    ∀ P : W.toAffine.Point, p • P = 0 → P = 0}

theorem mem_ssJSet_iff {p : ℕ} {K : Type*} [Field K] [DecidableEq K] {j : K} :
    j ∈ ssJSet p K ↔ ∀ (W : WeierstrassCurve K) [W.IsElliptic], W.j = j →
      ∀ P : W.toAffine.Point, p • P = 0 → P = 0 :=
  Iff.rfl

def ModuliPoint.IsSupersingular (p : ℕ) {N : ℕ} {K : Type*} [Field K] [DecidableEq K]
    (x : ModuliPoint N K) : Prop :=
  x.j ∈ ssJSet p K

def ssLocus (p N : ℕ) (K : Type*) [Field K] [DecidableEq K] : Set (ModuliPoint N K) :=
  {x | x.IsSupersingular p}

theorem mem_ssLocus_iff {p N : ℕ} {K : Type*} [Field K] [DecidableEq K]
    {x : ModuliPoint N K} :
    x ∈ ssLocus p N K ↔ x.j ∈ ssJSet p K :=
  Iff.rfl

theorem isSupersingular_mk_iff {p N : ℕ} {K : Type*} [Field K] [DecidableEq K]
    {P : Gamma0Pair N K} :
    ModuliPoint.IsSupersingular p (Quot.mk _ P : ModuliPoint N K) ↔
      P.toCurve.j ∈ ssJSet p K :=
  Iff.rfl

end ModularCurve
