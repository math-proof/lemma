-- LinearPart, Unit, End, and linearPartHom material split from
-- Lemma/MvFormalGroup/EndRingV2.lean so the core module can compile
-- without Def.MvFormalGroup_BasicV2 (blocked on the
-- Instance.MvFormalGroup_BasicV2 ↔ Def addMv cycle) or
-- Instance.MvFormalGroup_EndRingV2.
import Lemma.MvPowerSeries.EndRingV2
import Def.MvFormalGroup_BasicV2
import Instance.MvFormalGroup_EndRingV2

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {g h k : ℕ} {R : Type*} [CommRing R]

section LinearPart

@[simp]
theorem linearPart_zero :
    linearPart (fun _ : Fin h => (0 : MvPowerSeries (Fin g) R)) = 0 := by
  ext i j
  simp only [linearPart, Matrix.of_apply, Matrix.zero_apply]
  exact map_zero _

@[simp]
theorem linearPart_X :
    linearPart (fun i : Fin g => (X i : MvPowerSeries (Fin g) R)) = 1 := by
  ext i j
  simp only [linearPart, Matrix.of_apply, Matrix.one_apply]
  rw [coeff_X]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [ite_eq_right (fun hcon => hij (Finsupp.single_left_injective one_ne_zero hcon).symm),
      ite_eq_right hij]

theorem linearPart_subst {m n : ℕ} {b : Fin m → MvPowerSeries (Fin n) R}
    (hb : ∀ s, (b s).constantCoeff = 0) (a : Fin h → MvPowerSeries (Fin m) R) :
    linearPart (fun i => subst b (a i)) = linearPart a * linearPart b := by
  ext i j
  simp only [linearPart, Matrix.of_apply, Matrix.mul_apply]
  exact coeff_single_subst hb (a i) j

theorem linearPart_subst_elim {m : ℕ} (F : MvFormalGroup g R)
    {a b : Fin g → MvPowerSeries (Fin m) R}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0) :
    linearPart (fun i => subst (Sum.elim a b) (F.toPowerSeries i))
      = linearPart a + linearPart b := by
  classical
  have hab : ∀ s : Fin g ⊕ Fin g, ((Sum.elim a b) s).constantCoeff = 0 := by
    rintro (s | s)
    exacts [ha s, hb s]
  ext i j
  simp only [linearPart, Matrix.of_apply, Matrix.add_apply]
  rw [coeff_single_subst hab (F.toPowerSeries i) j, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, F.coeff_single_inl, F.coeff_single_inr,
    ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq, Finset.sum_ite_eq]
  simp

end LinearPart

namespace Hom

variable {F : MvFormalGroup g R} {G : MvFormalGroup h R}

theorem toPowerSeries_zero' : (0 : Hom F G).toPowerSeries = fun _ => 0 := rfl

end Hom

namespace End

variable (F : MvFormalGroup g R)

theorem toPowerSeries_one :
    Hom.toPowerSeries (1 : End F) = fun i => (X i : MvPowerSeries (Fin g) R) := rfl

@[simp]
theorem toPowerSeries_mul (φ ψ : End F) :
    Hom.toPowerSeries (φ * ψ)
      = fun i => subst (Hom.toPowerSeries ψ) (Hom.toPowerSeries φ i) := rfl


theorem toPowerSeries_natCast [IsComm F] (n : ℕ) :
    Hom.toPowerSeries ((n : End F)) = F.nthSeries n := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, nthSeries_zero]
    rfl
  | succ n ih =>
    rw [Nat.cast_succ]
    funext i
    show subst (Sum.elim (Hom.toPowerSeries ((n : End F)))
        (Hom.toPowerSeries (1 : End F))) (F.toPowerSeries i)
      = F.nthSeries (n + 1) i
    rw [ih, nthSeries_succ]
    rfl

@[simp]
theorem toPowerSeries_zero [IsComm F] :
    Hom.toPowerSeries (0 : End F) = fun _ => (0 : MvPowerSeries (Fin g) R) := rfl

@[simp]
theorem toPowerSeries_add [IsComm F] (φ ψ : End F) :
    Hom.toPowerSeries (φ + ψ)
      = fun i => subst (Sum.elim (Hom.toPowerSeries φ) (Hom.toPowerSeries ψ))
        (F.toPowerSeries i) := rfl

end End

theorem constantCoeff_nthSeries (F : MvFormalGroup g R) (n : ℕ) :
    ∀ i, (F.nthSeries n i).constantCoeff = 0 := by
  induction n with
  | zero =>
    intro i
    rw [nthSeries_zero]
    exact map_zero _
  | succ n ih =>
    intro i
    rw [nthSeries_succ]
    exact constantCoeff_subst_elim F ih (fun j => constantCoeff_X j) i

theorem linearPart_nthSeries (F : MvFormalGroup g R) (n : ℕ) :
    linearPart (F.nthSeries n) = n • (1 : Matrix (Fin g) (Fin g) R) := by
  induction n with
  | zero =>
    rw [nthSeries_zero, zero_smul]
    exact linearPart_zero
  | succ n ih =>
    rw [nthSeries_succ,
      linearPart_subst_elim F (constantCoeff_nthSeries F n) (fun j => constantCoeff_X j),
      ih, linearPart_X, succ_nsmul]

def linearPartHom (F : MvFormalGroup g R) [IsComm F] :
    End F →+* Matrix (Fin g) (Fin g) R where
  toFun φ := linearPart (Hom.toPowerSeries φ)
  map_one' := by
    show linearPart (fun i => (X i : MvPowerSeries (Fin g) R)) = 1
    exact linearPart_X
  map_mul' φ ψ := by
    show linearPart (fun i => subst (Hom.toPowerSeries ψ) (Hom.toPowerSeries φ i)) = _
    exact linearPart_subst (Hom.constantCoeff_eq_zero ψ) (Hom.toPowerSeries φ)
  map_zero' := by
    show linearPart (fun _ : Fin g => (0 : MvPowerSeries (Fin g) R)) = 0
    exact linearPart_zero
  map_add' φ ψ := by
    show linearPart (fun i => subst
        (Sum.elim (Hom.toPowerSeries φ) (Hom.toPowerSeries ψ)) (F.toPowerSeries i)) = _
    exact linearPart_subst_elim F (Hom.constantCoeff_eq_zero φ)
      (Hom.constantCoeff_eq_zero ψ)

@[simp]
theorem linearPartHom_apply (F : MvFormalGroup g R) [IsComm F] (φ : End F) :
    linearPartHom F φ = linearPart (Hom.toPowerSeries φ) := rfl

@[simp]
theorem linearPartHom_natCast (F : MvFormalGroup g R) [IsComm F] (n : ℕ) :
    linearPartHom F ((n : End F)) = n • (1 : Matrix (Fin g) (Fin g) R) := by
  rw [linearPartHom_apply, End.toPowerSeries_natCast, linearPart_nthSeries]

end MvFormalGroup
