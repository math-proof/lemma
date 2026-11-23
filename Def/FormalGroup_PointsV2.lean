module

public import Def.FormalGroup_NegV2
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.Finiteness.Ideal
public import Structure.MvFormalGroup_PointsV2
public import Def.MvFormalGroup_BasicV2
public import Instance.MvFormalGroup_EndRingV2

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {g h k : ℕ} {R : Type*} [CommRing R]

section AdicEval

variable {S : Type*} [CommRing S] [Algebra R S] {S' : Type*} [CommRing S'] [Algebra R S']
  {σ : Type*}

def adicEval (J : Ideal S) (x : σ → S) (f : MvPowerSeries σ R) : S :=
  letI : UniformSpace R := ⊥
  letI : WithIdeal S := ⟨J⟩
  MvPowerSeries.eval₂ (algebraMap R S) x f

def adicEvalAlgHom [Finite σ] (J : Ideal S) [IsAdicComplete J S] {x : σ → S}
    (hx : ∀ s, x s ∈ J.radical) : MvPowerSeries σ R →ₐ[R] S :=
  letI : UniformSpace R := ⊥
  letI : WithIdeal S := ⟨J⟩
  haveI : CompleteSpace S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).1
  haveI : T2Space S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).2
  haveI : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  MvPowerSeries.aeval (hasEval_of_mem_radical J hx)


end AdicEval

namespace Points

variable {F : MvFormalGroup g R} {S : Type*} [CommRing S] {J : Ideal S}

variable [Algebra R S]

variable [IsAdicComplete J S]

protected def add (x y : Points F S J) : Points F S J where
  val i := adicEval J (Sum.elim x.val y.val) (F.toPowerSeries i)
  mem_radical i := adicEval_mem_radical J (forall_sumElim x.mem_radical y.mem_radical)
    (F.constantCoeff_eq_zero i)

protected def neg (x : Points F S J) : Points F S J where
  val i := adicEval J x.val (invSeries F i)
  mem_radical i := adicEval_mem_radical J x.mem_radical (constantCoeff_invSeries F i)

end Points


namespace Hom

variable {F : MvFormalGroup g R} {G : MvFormalGroup h R} {H : MvFormalGroup k R}
  {S : Type*} [CommRing S] [Algebra R S] {J : Ideal S} [IsAdicComplete J S]

def evalPoints (φ : Hom F G) : Points F S J →+ Points G S J :=
  AddMonoidHom.mk'
    (fun x => ⟨fun i => adicEval J x.val (φ.toPowerSeries i),
      fun i => adicEval_mem_radical J x.mem_radical (φ.constantCoeff_eq_zero i)⟩)
    (fun x y => by
      ext i
      show adicEval J (fun j => adicEval J (Sum.elim x.val y.val) (F.toPowerSeries j))
          (φ.toPowerSeries i)
        = adicEval J (Sum.elim (fun j => adicEval J x.val (φ.toPowerSeries j))
          fun j => adicEval J y.val (φ.toPowerSeries j)) (G.toPowerSeries i)
      have hw : ∀ t, Sum.elim x.val y.val t ∈ J.radical :=
        forall_sumElim x.mem_radical y.mem_radical
      have hl : HasSubst (fun l : Fin g => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
        hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
      have hr : HasSubst (fun l : Fin g => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
        hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
      have hU : ∀ j, (subst (fun l : Fin g => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
          (φ.toPowerSeries j)).constantCoeff = 0 := fun j =>
        constantCoeff_subst_eq_zero hl (fun l => constantCoeff_X _) (φ.constantCoeff_eq_zero j)
      have hV : ∀ j, (subst (fun l : Fin g => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
          (φ.toPowerSeries j)).constantCoeff = 0 := fun j =>
        constantCoeff_subst_eq_zero hr (fun l => constantCoeff_X _) (φ.constantCoeff_eq_zero j)
      have hxa : (fun l => adicEval J (Sum.elim x.val y.val)
          (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) = x.val :=
        funext fun l => adicEval_X _ _ _
      have hyb : (fun l => adicEval J (Sum.elim x.val y.val)
          (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) = y.val :=
        funext fun l => adicEval_X _ _ _
      have hin1 : (fun j => adicEval J (Sum.elim x.val y.val)
          (subst (fun l : Fin g => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (φ.toPowerSeries j))) = fun j => adicEval J x.val (φ.toPowerSeries j) := by
        funext j
        rw [adicEval_subst J hw hl, hxa]
      have hin2 : (fun j => adicEval J (Sum.elim x.val y.val)
          (subst (fun l : Fin g => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (φ.toPowerSeries j))) = fun j => adicEval J y.val (φ.toPowerSeries j) := by
        funext j
        rw [adicEval_subst J hw hr, hyb]
      have key := congrArg (adicEval J (Sum.elim x.val y.val)) (φ.subst_eq i)
      rw [adicEval_subst J hw F.hasSubst_toPowerSeries, adicEval_subst_elim G J hw hU hV,
        hin1, hin2] at key
      exact key)

end Hom

namespace Points

variable {F : MvFormalGroup g R}
  {S : Type*} [CommRing S] [Algebra R S] {J : Ideal S} [IsAdicComplete J S]
  {S' : Type*} [CommRing S'] [Algebra R S'] {J' : Ideal S'} [IsAdicComplete J' S']

def map (φ : S →ₐ[R] S') (hJ : J.FG) (hφ : ∀ s ∈ J, φ s ∈ J'.radical) :
    Points F S J →+ Points F S' J' :=
  AddMonoidHom.mk'
    (fun x => ⟨fun i => φ (x.val i), fun i => map_mem_radical φ hφ (x.mem_radical i)⟩)
    (fun x y => by
      ext i
      show φ (adicEval J (Sum.elim x.val y.val) (F.toPowerSeries i))
          = adicEval J' (Sum.elim (fun j => φ (x.val j)) fun j => φ (y.val j))
            (F.toPowerSeries i)
      have hfam : (fun s => φ (Sum.elim x.val y.val s))
          = Sum.elim (fun j => φ (x.val j)) fun j => φ (y.val j) := by
        funext s
        rcases s with j | j <;> rfl
      rw [map_adicEval J J' φ hJ hφ (forall_sumElim x.mem_radical y.mem_radical), hfam])

end Points

namespace Hom

variable {F : MvFormalGroup g R} {G : MvFormalGroup h R}
  {S : Type*} [CommRing S] [Algebra R S] {J : Ideal S} [IsAdicComplete J S]
  {S' : Type*} [CommRing S'] [Algebra R S'] {J' : Ideal S'} [IsAdicComplete J' S']

end Hom

end MvFormalGroup

end
