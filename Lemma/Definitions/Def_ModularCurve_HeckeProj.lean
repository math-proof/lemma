import Lemma.Definitions.Def_HeckeGalois_EichlerShimura
import Lemma.Definitions.Def_CuspForm_HeckeAlgebra

noncomputable section

namespace ModularCurve

variable (N : ℕ) [NeZero N]

def heckeProjGen (ℓ : Nat.Primes) : CuspForm.heckeAlgebra N 2 ∅ :=
  if h : (ℓ : ℕ) ∣ N then CuspForm.heckeAlgebra.U ℓ.2 h (Set.notMem_empty _)
  else CuspForm.heckeAlgebra.T ℓ.2 h (Set.notMem_empty _)

def heckeProj : HeckeAlg →+* CuspForm.heckeAlgebra N 2 ∅ :=
  (MvPolynomial.aeval (R := ℤ) (heckeProjGen N)).toRingHom

variable {N}

theorem heckeProj_heckeGen_of_not_dvd (ℓ : Nat.Primes) (h : ¬ (ℓ : ℕ) ∣ N) :
    heckeProj N (heckeGen ℓ) = CuspForm.heckeAlgebra.T ℓ.2 h (Set.notMem_empty _) := by
  simp [heckeProj, heckeGen, heckeProjGen, h]

theorem heckeProj_heckeGen_of_dvd (ℓ : Nat.Primes) (h : (ℓ : ℕ) ∣ N) :
    heckeProj N (heckeGen ℓ) = CuspForm.heckeAlgebra.U ℓ.2 h (Set.notMem_empty _) := by
  simp [heckeProj, heckeGen, heckeProjGen, h]

theorem heckeProj_C (c : ℤ) : heckeProj N (MvPolynomial.C c) = algebraMap ℤ (CuspForm.heckeAlgebra N 2 ∅) c := by
  simp [heckeProj]

theorem ringHom_ext_heckeProj {R : Type*} [Ring R] {f g : CuspForm.heckeAlgebra N 2 ∅ →+* R}
    (h : ∀ ℓ : Nat.Primes, f (heckeProjGen N ℓ) = g (heckeProjGen N ℓ)) :
    f.comp (heckeProj N) = g.comp (heckeProj N) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    rw [RingHom.comp_apply, RingHom.comp_apply, heckeProj_C, eq_intCast, map_intCast, map_intCast]
  · intro ℓ
    simpa [heckeProj, heckeProjGen] using h ℓ

end ModularCurve

end
