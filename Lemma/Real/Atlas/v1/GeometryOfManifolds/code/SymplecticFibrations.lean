import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticFibrations
open DifferentialFormSpace


/--
[gompf_lefschetz_symplectic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticFibrations.lean)
-/
@[path]
lemma gompf_lefschetz_symplectic
  {Ω_M : ℕ → Type*}
  {Ω_B2 : ℕ → Type*}
  {Ω_F : ℕ → Type*}
  [inst_M : DifferentialFormSpace Ω_M VF_M]
  [inst_B2 : DifferentialFormSpace Ω_B2 VF_B2]
  [inst_F : DifferentialFormSpace Ω_F VF_F]
  [IsOriented Ω_M VF_M]
  [IsOriented Ω_B2 VF_B2]
-- given
  (lf : LefschetzFibration (inst_M := inst_M) (inst_B2 := inst_B2) (inst_F := inst_F))
  (hF : FiberClassNonzero lf) :
-- imply
  ∃ (S_M : SymplecticManifold Ω_M VF_M) (S_F : SymplecticManifold Ω_F VF_F), S_F.ω = lf.genericFiberInclusion.pullback S_M.ω ∧ IsSymplecticSubmanifold S_M lf.genericFiberInclusion :=
-- proof
  gompf_construction lf hF

/--
[IsLefschetzFibration.toLefschetzFibration](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticFibrations.lean)
-/
@[path]
lemma IsLefschetzFibration.toLefschetzFibration
  {Ω_M : ℕ → Type*}
  {Ω_B2 : ℕ → Type*}
  {Ω_F : ℕ → Type*}
  [inst_M : DifferentialFormSpace Ω_M VF_M]
  [inst_B2 : DifferentialFormSpace Ω_B2 VF_B2]
  [inst_F : DifferentialFormSpace Ω_F VF_F]
  [IsOriented Ω_M VF_M]
  [IsOriented Ω_B2 VF_B2]
  {f : DFSMorphism Ω_M VF_M Ω_B2 VF_B2}
  {fiberIncl : DFSMorphism Ω_F VF_F Ω_M VF_M}
-- given
  (hfib : IsLefschetzFibration f fiberIncl) :
-- imply
  ∃ (lf : LefschetzFibration (inst_M := inst_M) (inst_B2 := inst_B2) (inst_F := inst_F)), lf.f = f ∧ lf.genericFiberInclusion = fiberIncl := by
-- proof
  obtain ⟨lf, hf, hfi⟩ := hfib
  exact ⟨lf, hf, hfi⟩

/--
[IsSymplecticFibration.toSymplecticFibration](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticFibrations.lean)
-/
@[path]
lemma IsSymplecticFibration.toSymplecticFibration
  {Ω_M : ℕ → Type*}
  {Ω_B : ℕ → Type*}
  {Ω_F : ℕ → Type*}
  [inst_M : DifferentialFormSpace Ω_M VF_M]
  [inst_B : DifferentialFormSpace Ω_B VF_B]
  [inst_F : DifferentialFormSpace Ω_F VF_F]
  {f : DFSMorphism Ω_M VF_M Ω_B VF_B}
  {fiberIncl : DFSMorphism Ω_F VF_F Ω_M VF_M}
  {fiberSymp : SymplecticManifold Ω_F VF_F}
-- given
  (hfib : IsSymplecticFibration f fiberIncl fiberSymp) :
-- imply
  ∃ (fib : SymplecticFibration (inst_M := inst_M) (inst_B := inst_B) (inst_F := inst_F)), fib.f = f ∧ fib.fiberInclusion = fiberIncl ∧ fib.fiberSymplectic = fiberSymp :=
-- proof
  hfib

/--
[SymplecticFibration.transition_self_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticFibrations.lean)
-/
@[path]
lemma SymplecticFibration.transition_self_eq
  {Ω_M : ℕ → Type*}
  {Ω_B : ℕ → Type*}
  {Ω_F : ℕ → Type*}
  [inst_M : DifferentialFormSpace Ω_M VF_M]
  [inst_B : DifferentialFormSpace Ω_B VF_B]
  [inst_F : DifferentialFormSpace Ω_F VF_F]
  {i : fib.CoverIdx}
  {p : ℕ}
  {α : Ω_F p}
-- given
  (fib : SymplecticFibration (inst_M := inst_M) (inst_B := inst_B) (inst_F := inst_F)) :
-- imply
  (fib.transitionMap i i).pullback α = α := by
-- proof
  have h_inv := fib.transition_inverse i i α
  have h_cyc := fib.transition_cocycle i i i α
  rwa [h_cyc] at h_inv

/--
[SymplecticFibration.LocalTrivializationData.patching_restricts_to_fiber](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticFibrations.lean)
-/
@[path]
lemma SymplecticFibration.LocalTrivializationData.patching_restricts_to_fiber
  {Ω_M : ℕ → Type*}
  {Ω_B : ℕ → Type*}
  {Ω_F : ℕ → Type*}
  [inst_M : DifferentialFormSpace Ω_M VF_M]
  [inst_B : DifferentialFormSpace Ω_B VF_B]
  [inst_F : DifferentialFormSpace Ω_F VF_F]
  {fib : SymplecticFibration (inst_M := inst_M) (inst_B := inst_B) (inst_F := inst_F)}
  {triv : SymplecticFibration.LocalTrivializationData fib}
  {i j : fib.CoverIdx}
  {r₁ r₂ : ℝ}
-- given
  (hsum : r₁ + r₂ = 1)
  (h_η_restricts_via_i : fib.fiberInclusion.pullback ((triv.localProj i).pullback fib.fiberSymplectic.ω) = fib.fiberSymplectic.ω)
  (h_η_restricts_via_j : fib.fiberInclusion.pullback ((triv.localProj j).pullback fib.fiberSymplectic.ω) = fib.fiberSymplectic.ω) :
-- imply
  fib.fiberInclusion.pullback (r₁ • (triv.localProj i).pullback fib.fiberSymplectic.ω + r₂ • (triv.localProj j).pullback fib.fiberSymplectic.ω) = fib.fiberSymplectic.ω := by
-- proof
  rw [fib.fiberInclusion.pullback_add, fib.fiberInclusion.pullback_smul,
    fib.fiberInclusion.pullback_smul, h_η_restricts_via_i, h_η_restricts_via_j]
  rw [← add_smul, hsum, one_smul]


-- created on 2026-10-23
