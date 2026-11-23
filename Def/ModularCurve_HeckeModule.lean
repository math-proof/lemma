module

public import Theorem.LaurentSeries.HeckeOperatorTotal
public import Def.HeckeGalois_EichlerShimura

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open AlgebraicCurve

section Operators

variable (N : ℕ) [NeZero N]

def heckeOperatorBar (ℓ : Nat.Primes) : Module.End ℤ (JZero N) :=
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  (heckeOperatorAlong (AlgebraicClosure ℚ) N ℓ).toIntLinearMap

def HeckeOperatorsCommuteBar : Prop :=
  ∀ ℓ ℓ' : Nat.Primes,
    heckeOperatorBar N ℓ * heckeOperatorBar N ℓ' = heckeOperatorBar N ℓ' * heckeOperatorBar N ℓ

end Operators

section Eval

variable {N : ℕ} [NeZero N]

open scoped IsMulCommutative in

def heckeEvalBarAux (h : HeckeOperatorsCommuteBar N) :
    HeckeAlg →ₐ[ℤ] (Algebra.adjoin ℤ (Set.range (heckeOperatorBar N)) :
      Subalgebra ℤ (Module.End ℤ (JZero N))) :=
  haveI := isMulCommutative_adjoin_heckeOperatorBar h
  MvPolynomial.aeval fun ℓ =>
    (⟨heckeOperatorBar N ℓ, Algebra.subset_adjoin (Set.mem_range_self ℓ)⟩ :
      Algebra.adjoin ℤ (Set.range (heckeOperatorBar N)))

def heckeEvalBar (h : HeckeOperatorsCommuteBar N) : HeckeAlg →+* Module.End ℤ (JZero N) :=
  ((Algebra.adjoin ℤ (Set.range (heckeOperatorBar N))).val.comp (heckeEvalBarAux h)).toRingHom

end Eval

section TheModule

variable (N : ℕ) [NeZero N]

open Classical in

@[implicit_reducible]
def heckeModuleBar : Module HeckeAlg (JZero N) :=
  if h : HeckeOperatorsCommuteBar N then Module.compHom (JZero N) (heckeEvalBar h)
  else Module.compHom (JZero N) (MvPolynomial.eval₂Hom (Int.castRingHom ℤ) (0 : Nat.Primes → ℤ))

variable {N}

end TheModule

end ModularCurve

end

end
