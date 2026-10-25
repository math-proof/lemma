import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.ShermanAssembly2.Part2
open StatMech StatMech.Onsager


/--
[ons_turnW_omega_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanAssembly2.lean)
-/
@[path]
private lemma ons_turnW_omega_inv_eq
  {ω : ℂ}
  {μ ν : Fin 4} :
-- imply
  ons_turnW ω⁻¹ μ ν = (ons_turnW ω μ ν)⁻¹ := by
-- proof
  apply StatMech.Onsager.ons_turnW_omega_inv ω μ ν

/--
[ons_KWmat_dartRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanAssembly2.lean)
-/
@[path]
private lemma ons_KWmat_dartRev_eq
  {L : ℕ}
  {x ω : ℂ}
  {d₁ d₂ : ons_Dart L} :
-- imply
  ons_KWmat L x ω (ons_dartRev L d₁) (ons_dartRev L d₂) = ons_KWmat L x ω⁻¹ d₂ d₁ := by
-- proof
  apply StatMech.Onsager.ons_KWmat_dartRev L x ω d₁ d₂

/--
[ons_loopRev_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanAssembly2.lean)
-/
@[path]
private lemma ons_loopRev_involutive_eq
  {L n : ℕ}
  [NeZero n]
  {v : Fin n → ons_Dart L} :
-- imply
  ons_loopRev L (ons_loopRev L v) = v := by
-- proof
  apply StatMech.Onsager.ons_loopRev_involutive L n v

/--
[ons_visits_loopRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanAssembly2.lean)
-/
@[path]
private lemma ons_visits_loopRev_eq
  {L n : ℕ}
  [NeZero n]
  {v : Fin n → ons_Dart L}
  {d : ons_Dart L} :
-- imply
  (∃ i, ons_loopRev L v i = d) ↔ (∃ i, v i = ons_dartRev L d) := by
-- proof
  apply StatMech.Onsager.ons_visits_loopRev v d

/--
[ons_loopWeight_dartRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanAssembly2.lean)
-/
@[path]
private lemma ons_loopWeight_dartRev_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {x ω : ℂ}
  {v : Fin n → ons_Dart L} :
-- imply
  ons_loopWeight (ons_KWmat L x ω) (fun k => ons_dartRev L (v (-k))) = ons_loopWeight (ons_KWmat L x ω⁻¹) v := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_dartRev x ω v

/--
[ons_loopWeight_omega_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanAssembly2.lean)
-/
@[path]
private lemma ons_loopWeight_omega_inv_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {x ω : ℂ}
  {v : Fin n → ons_Dart L}
-- given
  (hω0 : ω ≠ 0)
  (hI : ω ^ 2 = Complex.I) :
-- imply
  ons_loopWeight (ons_KWmat L x ω⁻¹) v = ons_loopWeight (ons_KWmat L x ω) v := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_omega_inv x ω hω0 hI v

/--
[ons_loopWeight_loopRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanAssembly2.lean)
-/
@[path]
private lemma ons_loopWeight_loopRev_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {x ω : ℂ}
  {v : Fin n → ons_Dart L}
-- given
  (hI : ω ^ 2 = Complex.I) :
-- imply
  ons_loopWeight (ons_KWmat L x ω) (ons_loopRev L v) = ons_loopWeight (ons_KWmat L x ω) v := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_loopRev x ω hI v

/--
[ons_loopSum_symm_omega_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanAssembly2.lean)
-/
@[path]
private lemma ons_loopSum_symm_omega_inv_eq
  {L : ℕ}
  [NeZero L]
  {n : ℕ}
  [NeZero n]
  {x ω : ℂ}
  {e : ons_Dart L} :
-- imply
  (∑ v ∈ (Finset.univ.filter (fun v : Fin n → ons_Dart L => (∃ i, v i = e) ∧ ¬ ∃ j, v j = ons_dartRev L e)), ons_loopWeight (ons_KWmat L x ω) v) = ∑ v ∈ (Finset.univ.filter (fun v : Fin n → ons_Dart L => (∃ i, v i = ons_dartRev L e) ∧ ¬ ∃ j, v j = e)), ons_loopWeight (ons_KWmat L x ω⁻¹) v := by
-- proof
  apply StatMech.Onsager.ons_loopSum_symm_omega_inv x ω e

/--
[ons_loopSum_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanAssembly2.lean)
-/
@[path]
private lemma ons_loopSum_symm_eq
  {L : ℕ}
  [NeZero L]
  {n : ℕ}
  [NeZero n]
  {x ω : ℂ}
  {e : ons_Dart L}
-- given
  (hω : ω ^ 2 = Complex.I) :
-- imply
  (∑ v ∈ (Finset.univ.filter (fun v : Fin n → ons_Dart L => (∃ i, v i = e) ∧ ¬ ∃ j, v j = ons_dartRev L e)), ons_loopWeight (ons_KWmat L x ω) v) = ∑ v ∈ (Finset.univ.filter (fun v : Fin n → ons_Dart L => (∃ i, v i = ons_dartRev L e) ∧ ¬ ∃ j, v j = e)), ons_loopWeight (ons_KWmat L x ω) v := by
-- proof
  apply StatMech.Onsager.ons_loopSum_symm x ω hω e


-- created on 2026-10-23
