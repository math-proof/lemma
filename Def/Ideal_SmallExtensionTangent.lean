import Mathlib
import Instance.IsLocalRing_SmallExtensionTangent

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace IsLocalRing.SmallExtension

variable {T S : Type} [CommRing T] [CommRing S] (σ : T →+* S)

def fibreProd : Subring (T × T) :=
  RingHom.eqLocus (σ.comp (RingHom.fst T T)) (σ.comp (RingHom.snd T T))

def fst : fibreProd σ →+* T := (RingHom.fst T T).comp (fibreProd σ).subtype

def snd : fibreProd σ →+* T := (RingHom.snd T T).comp (fibreProd σ).subtype

def diag : T →+* fibreProd σ :=
  ((RingHom.id T).prod (RingHom.id T)).codRestrict (fibreProd σ) (fun _ => rfl)

def pair (a b : T) (h : σ a = σ b) : fibreProd σ := ⟨(a, b), h⟩

section Local

variable [IsLocalRing T]

def diagMax : Ideal (fibreProd σ) := Ideal.span (diag σ '' (maximalIdeal T : Set T))

abbrev Tangent : Type := fibreProd σ ⧸ diagMax σ

def mk : fibreProd σ →+* Tangent σ := Ideal.Quotient.mk _

def res : Tangent σ →+* ResidueField T :=
  Ideal.Quotient.lift (diagMax σ) ((residue T).comp (fst σ)) (fun x hx => by
    rw [RingHom.comp_apply, residue_eq_zero_iff]
    have hx' : x ∈ Ideal.span (diag σ '' (maximalIdeal T : Set T)) := hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx'
    · rintro y ⟨m, hm, rfl⟩; exact hm
    · simp
    · rintro y z - - hy hz; rw [map_add]; exact Ideal.add_mem _ hy hz
    · rintro c y - hy; rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ hy)

end Local


section Artinian

def fibreProdSubmodule : Submodule T (T × T) where
  carrier := fibreProd σ
  zero_mem' := (fibreProd σ).zero_mem
  add_mem' := fun ha hb => (fibreProd σ).add_mem ha hb
  smul_mem' := fun c x hx => by
    show σ (c • x).1 = σ (c • x).2
    rw [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, smul_eq_mul, map_mul, map_mul, show σ x.1 = σ x.2 from hx]

end Artinian

end IsLocalRing.SmallExtension

end
