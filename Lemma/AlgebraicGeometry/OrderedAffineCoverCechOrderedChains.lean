import Mathlib
import Lemma.AlgebraicGeometry.OrderedAffineCoverCech
import Lemma.AlgebraicGeometry.OrderedAffineCoverCechCup
import Lemma.AlgebraicGeometry.OrderedAffineCoverCochainPullback
import Lemma.AlgebraicGeometry.OrderedAffineCoverCechOrdered
import Instance.AlgebraicGeometry_OrderedAffineCoverCechOrderedChains
import Abbrev.AlgebraicGeometry_OrderedAffineCoverCechOrderedChains

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

namespace Scheme.OrderedAffineCover

variable {V : Scheme.{u}} (K : V.OrderedAffineCover)

def olin {M : Type*} [AddCommGroup M] (n : ℕ) (f : K.OIdx n → M) : K.OCh n →ₗ[ℤ] M :=
  Finsupp.lift M ℤ (K.OIdx n) f

theorem olin_single {M : Type*} [AddCommGroup M] (n : ℕ) (f : K.OIdx n → M) (u : K.OIdx n) :
    K.olin n f (Finsupp.single u 1) = f u := by
  simp [olin, Finsupp.lift_apply, Finsupp.sum_single_index]

def obd (n : ℕ) : K.OCh (n + 1) →ₗ[ℤ] K.OCh n :=
  K.olin (n + 1) fun u => ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ)) • Finsupp.single (K.oface u j) (1 : ℤ)

theorem obd_single (n : ℕ) (u : K.OIdx (n + 1)) :
    K.obd n (Finsupp.single u 1) = ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ)) • Finsupp.single (K.oface u j) (1 : ℤ) :=
  K.olin_single _ _ u

def ocone (m : K.ι) (n : ℕ) : K.OCh n →ₗ[ℤ] K.OCh (n + 1) :=
  K.olin n fun u => Finsupp.single (Fin.cons m u : K.OIdx (n + 1)) (1 : ℤ)

theorem ocone_single (m : K.ι) (n : ℕ) (u : K.OIdx n) :
    K.ocone m n (Finsupp.single u 1) = Finsupp.single (Fin.cons m u : K.OIdx (n + 1)) (1 : ℤ) :=
  K.olin_single _ _ u

def oesort (n : ℕ) : K.OCh n →ₗ[ℤ] K.OCh n :=
  K.olin n fun u => by
    classical
    exact if hinj : Function.Injective u then
      ((Equiv.Perm.sign (Tuple.sort u) : ℤˣ) : ℤ) • Finsupp.single (u ∘ Tuple.sort u : K.OIdx n) (1 : ℤ)
    else 0

theorem oesort_single_of_injective (n : ℕ) (u : K.OIdx n) (hinj : Function.Injective u) :
    K.oesort n (Finsupp.single u 1) =
      ((Equiv.Perm.sign (Tuple.sort u) : ℤˣ) : ℤ) • Finsupp.single (u ∘ Tuple.sort u : K.OIdx n) (1 : ℤ) := by
  classical
  rw [oesort, olin_single, dif_pos hinj]

theorem oesort_single_of_not_injective (n : ℕ) (u : K.OIdx n) (hinj : ¬ Function.Injective u) :
    K.oesort n (Finsupp.single u 1) = 0 := by
  classical
  rw [oesort, olin_single, dif_neg hinj]

def ohom : (n : ℕ) → (K.OIdx n → K.OCh (n + 1))
  | 0 => fun _ => 0
  | n + 1 => fun σ => K.ocone (σ 0) (n + 1)
      (Finsupp.single σ 1 - K.oesort (n + 1) (Finsupp.single σ 1) - K.olin n (ohom n) (K.obd n (Finsupp.single σ 1)))

theorem ohom_zero (σ : K.OIdx 0) : K.ohom 0 σ = 0 := rfl

theorem ohom_succ (n : ℕ) (σ : K.OIdx (n + 1)) :
    K.ohom (n + 1) σ = K.ocone (σ 0) (n + 1)
      (Finsupp.single σ 1 - K.oesort (n + 1) (Finsupp.single σ 1) - K.olin n (K.ohom n) (K.obd n (Finsupp.single σ 1))) :=
  rfl

def OSub {n k : ℕ} (u : K.OIdx n) (t : K.OIdx k) : Prop := ∀ j, ∃ i, u j = t i

theorem oSub_iff {n k : ℕ} (u : K.OIdx n) (t : K.OIdx k) : K.OSub u t ↔ ∀ j, ∃ i, u j = t i := Iff.rfl

theorem oSub_refl {n : ℕ} (t : K.OIdx n) : K.OSub t t := fun j => ⟨j, rfl⟩

theorem oSub_trans {n k l : ℕ} {u : K.OIdx n} {t : K.OIdx k} {s : K.OIdx l} (h : K.OSub u t) (h' : K.OSub t s) :
    K.OSub u s := fun j => by
  obtain ⟨i, hi⟩ := h j
  obtain ⟨i', hi'⟩ := h' i
  exact ⟨i', hi.trans hi'⟩

theorem ointer_le_ointer_of_oSub {n k : ℕ} {u : K.OIdx n} {t : K.OIdx k} (h : K.OSub u t) :
    K.ointer t ≤ K.ointer u :=
  le_iInf fun j => by
    obtain ⟨i, hi⟩ := h j
    rw [hi]
    exact iInf_le _ i

end Scheme.OrderedAffineCover

namespace OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)

def oresTo {n k : ℕ} (t : K.OIdx k) (u : K.OIdx n) : F.obj (K.ointer u) →ₗ[ℤ] F.obj (K.ointer t) := by
  classical
  exact if h : K.OSub u t then (F.res (K.ointer_le_ointer_of_oSub h)).toAddMonoidHom.toIntLinearMap else 0

theorem oresTo_apply_of_oSub {n k : ℕ} (t : K.OIdx k) (u : K.OIdx n) (h : K.OSub u t) (x : F.obj (K.ointer u)) :
    F.oresTo K t u x = F.res (K.ointer_le_ointer_of_oSub h) x := by
  classical
  simp only [oresTo, dif_pos h]
  rfl

theorem oresTo_apply_of_not_oSub {n k : ℕ} (t : K.OIdx k) (u : K.OIdx n) (h : ¬ K.OSub u t) (x : F.obj (K.ointer u)) :
    F.oresTo K t u x = 0 := by
  classical
  simp only [oresTo, dif_neg h, LinearMap.zero_apply]

def opair {k : ℕ} (t : K.OIdx k) (n : ℕ) (c : F.ocochain K n) : K.OCh n →ₗ[ℤ] F.obj (K.ointer t) :=
  K.olin n fun u => F.oresTo K t u (c u)

theorem opair_single {k : ℕ} (t : K.OIdx k) (n : ℕ) (c : F.ocochain K n) (u : K.OIdx n) :
    F.opair K t n c (Finsupp.single u 1) = F.oresTo K t u (c u) :=
  K.olin_single _ _ u

def ohtpy (n : ℕ) (c : F.ocochain K (n + 1)) : F.ocochain K n :=
  fun t => F.opair K t (n + 1) c (K.ohom n t)

theorem ohtpy_apply (n : ℕ) (c : F.ocochain K (n + 1)) (t : K.OIdx n) :
    F.ohtpy K n c t = F.opair K t (n + 1) c (K.ohom n t) := rfl

end OModulePresheaf

end AlgebraicGeometry

end
