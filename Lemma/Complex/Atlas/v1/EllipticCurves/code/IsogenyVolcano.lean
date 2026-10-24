import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.EllipticCurves.code.IsogenyVolcano
open Polynomial Finset CMConductorTrichotomy IsogenyVolcano CMIsogeny VolcanoStructure CMSetCardinality
open Elliptic_Curves Elliptic_Curves.Deuring


namespace CMConductorTrichotomy

/--
[coprime_dvd_prime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyVolcano.lean)
-/
@[path]
lemma coprime_dvd_prime
  {ℓ a b : ℕ}
-- given
  (hℓ : Nat.Prime ℓ)
  (hab : Nat.Coprime a b)
  (ha : a ∣ ℓ)
  (hb : b ∣ ℓ) :
-- imply
  (a = 1 ∧ b = 1) ∨ (a = 1 ∧ b = ℓ) ∨ (a = ℓ ∧ b = 1) := by
-- proof
  obtain ha1 | haℓ := hℓ.eq_one_or_self_of_dvd a ha
  · rcases hℓ.eq_one_or_self_of_dvd b hb with hb1 | hbℓ
    · exact Or.inl ⟨ha1, hb1⟩
    · exact Or.inr (Or.inl ⟨ha1, hbℓ⟩)
  · rcases hℓ.eq_one_or_self_of_dvd b hb with hb1 | hbℓ
    · exact Or.inr (Or.inr ⟨haℓ, hb1⟩)
    · exfalso; subst haℓ; subst hbℓ
      exact hℓ.one_lt.ne' (by rwa [Nat.Coprime, Nat.gcd_self] at hab)

end CMConductorTrichotomy

namespace CMConductorTrichotomy

/--
[isogeny_order_trichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyVolcano.lean)
-/
@[path]
lemma isogeny_order_trichotomy
  {ℓ : ℕ}
  {f f' : ℕ}
-- given
  (hℓ : Nat.Prime ℓ)
  (hf : 0 < f)
  (h0 : f ∣ ℓ * f')
  (h1 : f' ∣ ℓ * f) :
-- imply
  f = f' ∨ f = ℓ * f' ∨ f' = ℓ * f := by
-- proof
  set g := Nat.gcd f f'
  have hg : 0 < g := Nat.pos_of_ne_zero (Nat.gcd_ne_zero_left (by omega))
  set a := f / g
  set b := f' / g
  have hfa : f = g * a := (Nat.mul_div_cancel' (Nat.gcd_dvd_left f f')).symm
  have hfb : f' = g * b := (Nat.mul_div_cancel' (Nat.gcd_dvd_right f f')).symm
  have hab : Nat.Coprime a b := Nat.coprime_div_gcd_div_gcd hg
  have ha_dvd : a ∣ ℓ * b := by
    have : g * a ∣ g * (ℓ * b) := by
      have := h1; rw [hfa, hfb] at this
      rwa [mul_left_comm] at this
    exact (Nat.mul_dvd_mul_iff_left hg).mp this
  have hb_dvd : b ∣ ℓ * a := by
    have : g * b ∣ g * (ℓ * a) := by
      have := h2; rw [hfa, hfb] at this
      rwa [mul_left_comm] at this
    exact (Nat.mul_dvd_mul_iff_left hg).mp this
  have ha_dvd_ℓ : a ∣ ℓ := hab.dvd_of_dvd_mul_right ha_dvd
  have hb_dvd_ℓ : b ∣ ℓ := hab.symm.dvd_of_dvd_mul_right hb_dvd
  obtain ⟨ha1, hb1⟩ | ⟨ha1, hbℓ⟩ | ⟨haℓ, hb1⟩ := coprime_dvd_prime hℓ hab ha_dvd_ℓ hb_dvd_ℓ
  ·
    left; rw [hfa, hfb, ha1, hb1]
  ·
    right; right; rw [hfa, hfb, ha1, hbℓ, mul_one, mul_comm]
  ·
    right; left; rw [hfa, hfb, haℓ, hb1, mul_one, mul_comm]

end CMConductorTrichotomy

namespace CMConductorTrichotomy

/--
[classifyIsogeny_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyVolcano.lean)
-/
@[path]
lemma classifyIsogeny_horizontal
  {ℓ f f' : ℕ}
-- given
  (h : f = f') :
-- imply
  classifyIsogeny ℓ f f' = IsogenyType.horizontal := by
-- proof
  simp [classifyIsogeny, h]

end CMConductorTrichotomy

namespace CMConductorTrichotomy

/--
[classifyIsogeny_descending](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyVolcano.lean)
-/
@[path]
lemma classifyIsogeny_descending
  {ℓ : ℕ}
  {f f' : ℕ}
-- given
  (hℓ : 1 < ℓ)
  (hf' : 0 < f')
  (h : f = ℓ * f') :
-- imply
  classifyIsogeny ℓ f f' = IsogenyType.descending := by
-- proof
  simp only [classifyIsogeny]
  have hne : ¬(ℓ * f' = f') := by nlinarith
  simp only [↓reduceIte, h, hne]

end CMConductorTrichotomy

namespace CMConductorTrichotomy

/--
[classifyIsogeny_ascending](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyVolcano.lean)
-/
@[path]
lemma classifyIsogeny_ascending
  {ℓ : ℕ}
  {f f' : ℕ}
-- given
  (hℓ : 1 < ℓ)
  (hf : 0 < f)
  (h : f' = ℓ * f) :
-- imply
  classifyIsogeny ℓ f f' = IsogenyType.ascending := by
-- proof
  simp only [classifyIsogeny]
  have hne : ¬(f = f') := by nlinarith
  have hne2 : ¬(f = ℓ * f') := by
    intro heq; rw [h] at heq
    nlinarith [Nat.mul_le_mul_right f (show 1 ≤ ℓ from by omega)]
  simp only [hne, ↓reduceIte, hne2, ↓reduceIte]
end CMConductorTrichotomy


namespace IsogenyVolcano

/--
[level_val_eq_zero_of_depth_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyVolcano.lean)
-/
@[path]
lemma level_val_eq_zero_of_depth_zero
  {ℓ : ℕ}
  {vol : IsogenyVolcano ℓ}
  {v : vol.V}
-- given
  (hd : vol.depth = 0) :
-- imply
  (vol.level v : ℕ) = 0 := by
-- proof
  have := (vol.level v).isLt
  omega
/-- For a floor vertex (level equal to `depth`, with positive depth), the number of
non-ascending edges is `0`: floor vertices have only their unique ascending edge. -/
end IsogenyVolcano


namespace CMIsogeny

/--
[surface_total_count](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyVolcano.lean)
-/
@[path]
lemma surface_total_count
  {C : CMIsogenyData}
  {S : SurfaceIsogenyCounts C} :
-- imply
  (S.numHorizontal : ℤ) + S.numDescending + S.numAscending = C.ℓ + 1 := by
-- proof
  rw [S.horizontal_eq, S.descending_eq, S.ascending_eq]
  push_cast
  ring

end CMIsogeny

namespace CMIsogeny

/--
[nonsurface_total_count](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyVolcano.lean)
-/
@[path]
lemma nonsurface_total_count
  {C : CMIsogenyData}
  {N : NonSurfaceIsogenyCounts C} :
-- imply
  (N.numHorizontal : ℤ) + N.numDescending + N.numAscending = C.ℓ + 1 := by
-- proof
  rw [N.horizontal_eq, N.descending_eq, N.ascending_eq]
  push_cast
  ring
end CMIsogeny


namespace VolcanoStructure

/--
[surface_conductor_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyVolcano.lean)
-/
@[path]
lemma surface_conductor_eq
  {C : OrdinaryIsogenyComponent}
  {K : KohelVolcano C}
  {v : K.volcano.V}
-- given
  (hv : (K.volcano.level v : ℕ) = 0) :
-- imply
  K.conductor v = C.f₀ := by
-- proof
  rw [K.conductor_eq_level v]
  simp [hv]

end VolcanoStructure

namespace VolcanoStructure

/--
[floor_conductor_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyVolcano.lean)
-/
@[path]
lemma floor_conductor_eq
  {C : OrdinaryIsogenyComponent}
  {K : KohelVolcano C}
  {v : K.volcano.V}
-- given
  (hv : (K.volcano.level v : ℕ) = K.volcano.depth) :
-- imply
  K.conductor v = C.f₀ * C.ℓ ^ K.volcano.depth := by
-- proof
  rw [K.conductor_eq_level v]
  simp [hv]

end VolcanoStructure

namespace VolcanoStructure

variable {C : OrdinaryIsogenyComponent} (K : KohelVolcano C)
/--
[conductor_increases_by_ℓ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyVolcano.lean)
-/
@[path]
lemma conductor_increases_by_ℓ (v w : K.volcano.V)
  (hv : (K.volcano.level v : ℕ) + 1 = (K.volcano.level w : ℕ))
  (_hlt : (K.volcano.level v : ℕ) < K.volcano.depth) :
  K.conductor w = C.ℓ * K.conductor v := by
  have hvi := K.conductor_eq_level v
  have hwi := K.conductor_eq_level w
  rw [hvi, hwi]
  have : (K.volcano.level w : ℕ) = (K.volcano.level v : ℕ) + 1 := hv.symm
  rw [this, pow_succ]
  ring

end VolcanoStructure

namespace VolcanoStructure

/--
[surface_degree_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyVolcano.lean)
-/
@[path]
lemma surface_degree_le_two
  {C : OrdinaryIsogenyComponent}
  {K : KohelVolcano C} :
-- imply
  K.volcano.surfaceDegree ≤ 2 :=
-- proof
  K.volcano.surfaceDegree_le
/-- For a surface vertex, the crater degree equals `1 + (D₀/ℓ)`. -/
end VolcanoStructure
namespace CMSetCardinality
open Elliptic_Curves Elliptic_Curves.Deuring


namespace CMSetCardinality

/--
[ellCMSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyVolcano.lean)
-/
@[path]
lemma ellCMSet_finite
  {D : ℤ}
  {F : Type*}
  [Field F]
  [Fintype F] :
-- imply
  Set.Finite (ellCMSet D F) :=
-- proof
  Set.toFinite _

end CMSetCardinality

namespace CMSetCardinality

/--
[orderContains_isDisc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyVolcano.lean)
-/
@[path]
lemma orderContains_isDisc
  {D D' : ℤ}
-- given
  (_hD : IsImagQuadDiscriminant D)
  (hcontains : OrderContains D D') :
-- imply
  IsImagQuadDiscriminant D' :=
-- proof
  hcontains.2

end CMSetCardinality

namespace CMSetCardinality

/--
[coprime_of_orderContains](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyVolcano.lean)
-/
@[path]
lemma coprime_of_orderContains
  {D D' : ℤ}
  {q : ℕ}
-- given
  (hcop : Nat.Coprime q D.natAbs)
  (hcontains : OrderContains D D') :
-- imply
  Nat.Coprime q D'.natAbs := by
-- proof
  obtain ⟨⟨u, _, hD⟩, _⟩ := hcontains
  rw [Nat.Coprime] at hcop ⊢
  have hdvd : D'.natAbs ∣ D.natAbs := by
    rw [hD]
    simp only [Int.natAbs_mul, Int.natAbs_pow]
    exact Dvd.intro_left (u.natAbs ^ 2) rfl
  exact Nat.Coprime.coprime_dvd_right hdvd hcop

end CMSetCardinality

namespace CMSetCardinality

/--
[normEquation_of_orderContains](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyVolcano.lean)
-/
@[path]
lemma normEquation_of_orderContains
  {D D' : ℤ}
  {q : ℕ}
  {t v : ℤ}
-- given
  (hne : Elliptic_Curves.NormEquation D q t v)
  (hcontains : OrderContains D D') :
-- imply
  ∃ w : ℤ, Elliptic_Curves.NormEquation D' q t w := by
-- proof
  obtain ⟨⟨u, _, hD⟩, _⟩ := hcontains
  refine ⟨u * v, ?_⟩
  simp only [Elliptic_Curves.NormEquation] at hne ⊢
  rw [hD] at hne
  ring_nf at hne ⊢
  linarith
/-- If `(D, q)` admits a norm-equation solution `(t, v)` with `q ∤ t`, then
`ellCMSet D F` is nonempty for every field `F` of size `q`. -/
end CMSetCardinality
namespace IsogenyCount
open Elliptic_Curves Elliptic_Curves.Deuring


/--
[conductor_increases_by_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyVolcano.lean)
-/
@[path]
private lemma conductor_increases_by__eq
  {C : OrdinaryIsogenyComponent}
  {K : KohelVolcano C}
  {v w : K.volcano.V}
-- given
  (hv : (K.volcano.level v : ℕ) + 1 = (K.volcano.level w : ℕ))
  (_hlt : (K.volcano.level v : ℕ) < K.volcano.depth) :
-- imply
  K.conductor w = C.ℓ * K.conductor v := by
-- proof
  apply VolcanoStructure.conductor_increases_by_ K v w hv _hlt


-- created on 2026-10-23
