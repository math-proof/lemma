module

public import Theorem.LaurentSeries.HeckeOperatorTotal
public import Def.HeckeGalois_EichlerShimura

public noncomputable section

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open AlgebraicCurve

section Operators

variable (N : ℕ) [NeZero N]


public theorem heckeOperatorBar_apply (ℓ : Nat.Primes) (x : JZero N) :
    heckeOperatorBar N ℓ x =
      (haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩; heckeOperatorAlong (AlgebraicClosure ℚ) N ℓ x) :=
  rfl


public theorem isMulCommutative_adjoin_heckeOperatorBar (h : HeckeOperatorsCommuteBar N) :
    IsMulCommutative (Algebra.adjoin ℤ (Set.range (heckeOperatorBar N))) :=
  Algebra.isMulCommutative_adjoin ℤ (by
    rintro _ ⟨ℓ, rfl⟩ _ ⟨ℓ', rfl⟩
    exact h ℓ ℓ')

open scoped IsMulCommutative in


public theorem heckeEvalBar_apply (h : HeckeOperatorsCommuteBar N) (t : HeckeAlg) :
    heckeEvalBar h t = (heckeEvalBarAux h t : Module.End ℤ (JZero N)) :=
  rfl

open scoped IsMulCommutative in

public theorem heckeEvalBarAux_heckeGen (h : HeckeOperatorsCommuteBar N) (ℓ : Nat.Primes) :
    heckeEvalBarAux h (heckeGen ℓ) =
      ⟨heckeOperatorBar N ℓ, Algebra.subset_adjoin (Set.mem_range_self ℓ)⟩ :=
  haveI := isMulCommutative_adjoin_heckeOperatorBar h
  MvPolynomial.aeval_X _ ℓ


public theorem heckeEvalBar_heckeGen (h : HeckeOperatorsCommuteBar N) (ℓ : Nat.Primes) :
    heckeEvalBar h (heckeGen ℓ) = heckeOperatorBar N ℓ := by
  rw [heckeEvalBar_apply, heckeEvalBarAux_heckeGen]


public theorem heckeEvalBar_C (h : HeckeOperatorsCommuteBar N) (a : ℤ) :
    heckeEvalBar h (MvPolynomial.C a) = (a : Module.End ℤ (JZero N)) := by
  rw [← MvPolynomial.algebraMap_eq, eq_intCast, map_intCast]

end Eval

section TheModule

variable (N : ℕ) [NeZero N]

open Classical in


public theorem heckeModuleBar_smul_def (h : HeckeOperatorsCommuteBar N) (t : HeckeAlg) (x : JZero N) :
    (letI := heckeModuleBar N; t • x) = heckeEvalBar h t x := by
  have e : heckeModuleBar N = Module.compHom (JZero N) (heckeEvalBar h) := dif_pos h
  rw [e]
  rfl


public theorem heckeModuleBar_heckeGen_smul (h : HeckeOperatorsCommuteBar N) (ℓ : Nat.Primes)
    (x : JZero N) : (letI := heckeModuleBar N; heckeGen ℓ • x) = heckeOperatorBar N ℓ x := by
  rw [heckeModuleBar_smul_def h, heckeEvalBar_heckeGen]


public theorem heckeModuleBar_smul_of_not (h : ¬ HeckeOperatorsCommuteBar N) (t : HeckeAlg) (x : JZero N) :
    (letI := heckeModuleBar N; t • x) = MvPolynomial.constantCoeff t • x := by
  have e : heckeModuleBar N =
      Module.compHom (JZero N)
        (MvPolynomial.eval₂Hom (Int.castRingHom ℤ) (0 : Nat.Primes → ℤ)) :=
    dif_neg h
  rw [e]
  show (MvPolynomial.eval₂Hom (Int.castRingHom ℤ) (0 : Nat.Primes → ℤ) t) • x = _
  rw [MvPolynomial.eval₂Hom_zero_apply, eq_intCast, Int.cast_id]


public theorem heckeModuleBar_heckeGen_smul_of_not (h : ¬ HeckeOperatorsCommuteBar N) (ℓ : Nat.Primes)
    (x : JZero N) : (letI := heckeModuleBar N; heckeGen ℓ • x) = 0 := by
  rw [heckeModuleBar_smul_of_not h, heckeGen, MvPolynomial.constantCoeff_X, zero_zsmul]


public theorem heckeModuleBar_C_smul (a : ℤ) (x : JZero N) :
    (letI := heckeModuleBar N; (MvPolynomial.C a : HeckeAlg) • x) = a • x := by
  by_cases h : HeckeOperatorsCommuteBar N
  · rw [heckeModuleBar_smul_def h, heckeEvalBar_C, Module.End.intCast_apply]
  · rw [heckeModuleBar_smul_of_not h, MvPolynomial.constantCoeff_C]

end TheModule

end ModularCurve

end
