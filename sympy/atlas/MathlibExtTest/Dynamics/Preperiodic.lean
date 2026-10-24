/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Dynamics/Preperiodic.lean -/

import sympy.atlas.Dynamics.Preperiodic
import Lemma.Set.Preperiodic
import Lean.Elab.Tactic.Omega

example : Function.forwardOrbit (id : ℕ → ℕ) 5 = {5} := by
  ext y
  simp [Function.forwardOrbit]

example : Function.IsPreperiodicPt (fun x : ℕ => x) 5 := by
  rw [Function.isPreperiodicPt_iff_exists_eq_iterate]
  exact ⟨0, 1, Nat.zero_lt_one, rfl⟩

example : (5 : ℕ) ∈ Function.periodicPts id :=
  Function.mk_mem_periodicPts Nat.zero_lt_one (Function.is_periodic_id 1 5)

example : ¬Function.IsStrictlyPreperiodicPt id (5 : ℕ) := by
  rintro ⟨_, hnot⟩
  exact hnot (Function.mk_mem_periodicPts Nat.zero_lt_one (Function.is_periodic_id 1 5))

example : Function.IsPreperiodicPt (fun _ : ℕ => 0) 7 := by
  rw [Function.isPreperiodicPt_iff_exists_eq_iterate]
  exact ⟨1, 2, by omega, rfl⟩

example : Function.IsPreperiodicPtOfType (fun _ : ℕ => (0 : ℕ)) 1 1 7 := by
  constructor
  · omega
  · rfl

private def swap : Bool → Bool
  | true => false
  | false => true

example : Function.IsPeriodicPt swap 2 true := by
  rfl

example : ¬Function.IsPeriodicPt swap 1 true := by
  decide

example : false ∈ Function.forwardOrbit swap true :=
  ⟨1, rfl⟩

example : Function.IsPreperiodicPt swap true := by
  rw [Function.isPreperiodicPt_iff_exists_eq_iterate]
  exact ⟨0, 2, by omega, rfl⟩

private def tailMap (_ : ℕ) : ℕ := 1

example : Function.IsStrictlyPreperiodicPt tailMap 0 := by
  constructor
  · rw [Function.isPreperiodicPt_iff_exists_eq_iterate]
    exact ⟨1, 2, by omega, rfl⟩
  · rw [Function.mem_periodicPts]
    rintro ⟨n, hn, hperiodic⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    change tailMap^[k + 1] 0 = 0 at hperiodic
    rw [Function.iterate_succ_apply'] at hperiodic
    simp [tailMap] at hperiodic

example : Function.IsPreperiodicPtOfType tailMap 1 1 0 := by
  exact ⟨by omega, rfl⟩

example : ¬Function.IsPreperiodicPtOfType tailMap 1 0 0 := by
  simp [Function.IsPreperiodicPtOfType]

example :
    Function.IsPreperiodicPtOfType tailMap 1 1 0 ↔
      0 < 1 ∧ Function.IsPeriodicPt tailMap 1 (tailMap^[1] 0) :=
  Function.isPreperiodicPtOfType_iff_isPeriodicPt

example : Function.GrandOrbitRel tailMap 0 1 :=
  ⟨1, 0, rfl⟩

example : (Function.forwardOrbit tailMap 0 ∩ Function.forwardOrbit tailMap 1).Nonempty := by
  rw [← Function.grandOrbitRel_iff_inter_nonempty]
  exact ⟨1, 0, rfl⟩

example : Function.GrandOrbitRel (id : ℕ → ℕ) 3 3 :=
  Function.grandOrbitRel_refl _ _

example : Function.GrandOrbitRel (id : ℕ → ℕ) 3 4 → False := by
  simp [Function.GrandOrbitRel]

example : Function.grandOrbit tailMap 0 = {y | Function.GrandOrbitRel tailMap 0 y} := rfl
