import Mathlib
import Instance.AlgebraicGeometry_DoubleComplex
import Structure.AlgebraicGeometry_DoubleComplex
import Abbrev.AlgebraicGeometry_DoubleComplex

set_option autoImplicit false

noncomputable section

universe u

namespace DoubleComplex


section Tot

variable {R : Type u} [CommRing R] (D : Bounded R)

def dTotH {n : ℕ} (i : Diag (n + 1)) :
    Tot D n →ₗ[R] D.C i.1.1 i.1.2 :=
  match i with
  | ⟨(0, _), _⟩ => 0
  | ⟨(p' + 1, q), h⟩ => (D.dH p' q).comp
      (LinearMap.proj (R := R)
        (φ := fun j : Diag n => D.C j.1.1 j.1.2) ⟨(p', q), by omega⟩)

def dTotV {n : ℕ} (i : Diag (n + 1)) :
    Tot D n →ₗ[R] D.C i.1.1 i.1.2 :=
  match i with
  | ⟨(_, 0), _⟩ => 0
  | ⟨(p, q' + 1), h⟩ => (D.dV p q').comp
      (LinearMap.proj (R := R)
        (φ := fun j : Diag n => D.C j.1.1 j.1.2) ⟨(p, q'), by omega⟩)

def dTot (n : ℕ) :
    Tot D n →ₗ[R] Tot D (n + 1) :=
  LinearMap.pi fun i =>
    dTotH D i + ((-1 : ℤ) ^ i.1.1) • dTotV D i

def HTotB : (n : ℕ) → Submodule R (LinearMap.ker (dTot D n))
  | 0 => ⊥
  | n' + 1 => (LinearMap.range (dTot D n')).comap
      (LinearMap.ker (dTot D (n' + 1))).subtype

abbrev HTot (n : ℕ) : Type u :=
  LinearMap.ker (dTot D n) ⧸ HTotB D n

end Tot

section DTotGeneric

variable {R : Type u} [CommRing R] {D : Bounded R}

theorem dTot_apply_zero_succ {n q' : ℕ} (h : 0 + (q' + 1) = n + 1)
    (c : Tot D n) :
    dTot D n c ⟨(0, q' + 1), h⟩ = D.dV 0 q' (c ⟨(0, q'), by omega⟩) := by
  simp only [dTot, LinearMap.pi_apply, LinearMap.add_apply,
    LinearMap.smul_apply, dTotH, dTotV, LinearMap.zero_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, pow_zero, one_smul, zero_add]

theorem dTot_apply_succ_zero {n p' : ℕ} (h : p' + 1 + 0 = n + 1)
    (c : Tot D n) :
    dTot D n c ⟨(p' + 1, 0), h⟩ = D.dH p' 0 (c ⟨(p', 0), by omega⟩) := by
  simp only [dTot, LinearMap.pi_apply, LinearMap.add_apply,
    LinearMap.smul_apply, dTotH, dTotV, LinearMap.zero_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, smul_zero, add_zero]

theorem dTot_apply_succ_succ {n p' q' : ℕ} (h : p' + 1 + (q' + 1) = n + 1)
    (c : Tot D n) :
    dTot D n c ⟨(p' + 1, q' + 1), h⟩
      = D.dH p' (q' + 1) (c ⟨(p', q' + 1), by omega⟩)
        + ((-1 : ℤ) ^ (p' + 1)) • D.dV (p' + 1) q' (c ⟨(p' + 1, q'), by omega⟩) := by
  rfl

theorem dTot_comp_dTot (D : Bounded R) (n : ℕ) :
    dTot D (n + 1) ∘ₗ dTot D n = 0 := by
  refine LinearMap.ext fun c => funext fun ⟨⟨pp, q⟩, h⟩ => ?_
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply]
  match pp, q, h with
  | 0, 0, h => omega
  | 0, q' + 1, h =>
    obtain ⟨q'', rfl⟩ : ∃ q'', q' = q'' + 1 := ⟨q' - 1, by omega⟩
    rw [dTot_apply_zero_succ, dTot_apply_zero_succ,
      ← LinearMap.comp_apply, D.dV_sq, LinearMap.zero_apply]
  | p' + 1, 0, h =>
    obtain ⟨p'', rfl⟩ : ∃ p'', p' = p'' + 1 := ⟨p' - 1, by omega⟩
    rw [dTot_apply_succ_zero, dTot_apply_succ_zero,
      ← LinearMap.comp_apply, D.dH_sq, LinearMap.zero_apply]
  | p' + 1, q' + 1, h =>
    rw [dTot_apply_succ_succ]
    have hH : D.dH p' (q' + 1) (dTot D n c ⟨(p', q' + 1), by omega⟩)
        = ((-1 : ℤ) ^ p') • D.dH p' (q' + 1) (D.dV p' q' (c ⟨(p', q'), by omega⟩)) := by
      rcases p' with _ | p''
      · rw [dTot_apply_zero_succ, pow_zero, one_smul]
      · rw [dTot_apply_succ_succ, map_add, map_zsmul,
          ← LinearMap.comp_apply, D.dH_sq, LinearMap.zero_apply, zero_add]
    have hV : D.dV (p' + 1) q' (dTot D n c ⟨(p' + 1, q'), by omega⟩)
        = D.dV (p' + 1) q' (D.dH p' q' (c ⟨(p', q'), by omega⟩)) := by
      rcases q' with _ | q''
      · rw [dTot_apply_succ_zero]
      · rw [dTot_apply_succ_succ, map_add, map_zsmul,
          show D.dV (p' + 1) (q'' + 1) (D.dV (p' + 1) q'' (c ⟨(p' + 1, q''), by omega⟩)) = 0 from
            LinearMap.congr_fun (D.dV_sq (p' + 1) q'') _, smul_zero, add_zero]
    rw [hH, hV,
      show D.dV (p' + 1) q' (D.dH p' q' (c ⟨(p', q'), by omega⟩))
        = D.dH p' (q' + 1) (D.dV p' q' (c ⟨(p', q'), by omega⟩)) from
        LinearMap.congr_fun (D.dHV_comm p' q') _,
      ← add_smul, show ((-1:ℤ)^p' + (-1)^(p'+1)) = 0 from by ring, zero_smul]

end DTotGeneric

section E2

variable {R : Type u} [CommRing R] (D : Bounded R)

def colB (p : ℕ) : (q : ℕ) → Submodule R (LinearMap.ker (D.dV p q))
  | 0 => ⊥
  | q' + 1 => (LinearMap.range (D.dV p q')).comap (LinearMap.ker (D.dV p (q' + 1))).subtype

abbrev colH (p q : ℕ) : Type u :=
  LinearMap.ker (D.dV p q) ⧸ colB D p q

def colHdH (p q : ℕ) :
    colH D p q →ₗ[R] colH D (p + 1) q :=
  Submodule.mapQ _ _
    ((D.dH p q).restrict fun x hx => LinearMap.mem_ker.mpr <| by
      rw [← LinearMap.comp_apply, D.dHV_comm, LinearMap.comp_apply,
        LinearMap.mem_ker.mp hx, map_zero])
    (by
      rcases q with _ | q'
      · simp only [colB]; exact bot_le
      · rintro x ⟨y, hy⟩
        exact ⟨D.dH p q' y, by
          show D.dV (p + 1) q' (D.dH p q' y) = D.dH p (q' + 1) x.1
          rw [← LinearMap.comp_apply, D.dHV_comm, LinearMap.comp_apply, hy]; rfl⟩)

def E₂IB :
    (p q : ℕ) → Submodule R (LinearMap.ker (colHdH D p q))
  | 0, _ => ⊥
  | p' + 1, q => (LinearMap.range (colHdH D p' q)).comap
      (LinearMap.ker (colHdH D (p' + 1) q)).subtype

abbrev E₂I (p q : ℕ) : Type u :=
  LinearMap.ker (colHdH D p q) ⧸ E₂IB D p q

def transpose : Bounded R where
  C a b := D.C b a
  dH a b := D.dV b a
  dV a b := D.dH b a
  dH_sq a b := D.dV_sq b a
  dV_sq a b := D.dH_sq b a
  dHV_comm a b := (D.dHV_comm b a).symm
  N := D.N
  hBound a b h := D.hBound b a h.symm

abbrev E₂II (p q : ℕ) : Type u :=
  E₂I (transpose D) q p

end E2


def BoundedSpectralSequence : Prop :=
  ∀ (R : Type u) [CommRing R] (D : Bounded R),
    Nonempty (Convergence R (E₂I D) (HTot D) D.N)

end DoubleComplex

end
