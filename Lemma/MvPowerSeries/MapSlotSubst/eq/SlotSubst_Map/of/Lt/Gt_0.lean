import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_ModularCurve_TateSlots
import Lemma.Int.P2MUtil

open ModularCurve

/--
[ModularCurve_map_slotSubst](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_map_slotSubst.lean)
-/

private lemma  hasSubst_slotFamily {K : Type*} [CommRing K] (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
  MvPowerSeries.HasSubst (slotFamily K p c j) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by
    fin_cases i
    ·
      show PowerSeries.constantCoeff (PowerSeries.C (c : K) * PowerSeries.X ^ j) = 0
      simp [hj.ne']
    ·
      show PowerSeries.constantCoeff (PowerSeries.C ((c⁻¹ : Kˣ) : K) * PowerSeries.X ^ (p - j)) = 0
      simp [(Nat.sub_pos_of_lt hjp).ne'])

private lemma  slotSubst_eq_subst_map {K : Type*} [CommRing K] (p : ℕ) (c : Kˣ) (j : ℕ)
  (h : MvPowerSeries.HasSubst (slotFamily K p c j)) (f : MvPowerSeries (Fin 2) ℤ) :
  slotSubst K p c j f =
    MvPowerSeries.subst (slotFamily K p c j) (MvPowerSeries.map (algebraMap ℤ K) f) := by
  rw [MvPowerSeries.map_algebraMap_eq_subst_X,
    MvPowerSeries.subst_comp_subst_apply MvPowerSeries.HasSubst.X h, slotSubst]
  congr 1
  funext s
  rw [MvPowerSeries.subst_X h]

private lemma  map_slotFamily {A B : Type*} [CommRing A] [CommRing B] (g : A →+* B) (p : ℕ) (c : Aˣ) (j : ℕ)
  (i : Fin 2) : PowerSeries.map g (slotFamily A p c j i) = slotFamily B p (Units.map (g : A →* B) c) j i := by
  fin_cases i <;> simp [slotFamily, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X, Units.coe_map,
    Units.coe_map_inv]


@[path]
private lemma main
  {A B : Type} [CommRing A] [CommRing B]
  {g : A →+* B}
  {p : ℕ}
  {c : Aˣ}
  {j : ℕ}
  {f : MvPowerSeries (Fin 2) ℤ}
-- given
  (hj : 0 < j)
  (hjp : j < p) :
-- imply
  (ModularCurve.slotSubst A p c j f).map g = ModularCurve.slotSubst B p (Units.map (g : A →* B) c) j f := by
-- proof
  have hA := hasSubst_slotFamily p c j hj hjp
  have hB := hasSubst_slotFamily p (Units.map (g : A →* B) c) j hj hjp
  rw [slotSubst_eq_subst_map _ _ _ hA, slotSubst_eq_subst_map _ _ _ hB, PowerSeries.map,
    MvPowerSeries.map_subst hA, MvPowerSeries.map_map]
  have hcomp : g.comp (algebraMap ℤ A) = algebraMap ℤ B := RingHom.ext_int _ _
  rw [hcomp]
  congr 1
  funext i
  exact map_slotFamily g p c j i


-- created on 2026-10-23
