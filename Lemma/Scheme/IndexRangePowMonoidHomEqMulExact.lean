import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[MonoidHom_index_range_powMonoidHom_eq_mul_of_exact](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_MonoidHom_index_range_powMonoidHom_eq_mul_of_exact.lean)
-/
@[path]
private lemma main
  [CommGroup G] [CommGroup U] [CommGroup F]
  (ι : MonoidHom U G)
  (φ : MonoidHom G F)
  {n : ℕ}
  -- given
  (hι : Function.Injective ι)
  (hφ : Function.Surjective φ)
  (hexact : ι.range = φ.ker)
  (hF : ∀ x : F, x ^ n = 1 → x = 1) :
  -- imply
  (powMonoidHom n : MonoidHom G G).range.index =
    (powMonoidHom n : MonoidHom F F).range.index * (powMonoidHom n : MonoidHom U U).range.index := by
  -- proof
  classical
  have h1 : φ.ker ⊔ (powMonoidHom n : MonoidHom G G).range = ((powMonoidHom n : MonoidHom F F).range).comap φ := by
    apply le_antisymm
    ·
      refine sup_le ?_ ?_
      ·
        intro g hg
        rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hg]
        apply one_mem _
      ·
        rintro _ ⟨g, rfl⟩
        rw [Subgroup.mem_comap, powMonoidHom_apply, map_pow]
        refine ⟨φ g, rfl⟩
    ·
      intro g hg
      rw [Subgroup.mem_comap] at hg
      obtain ⟨z, hz⟩ := hg
      obtain ⟨g', rfl⟩ := hφ z
      rw [powMonoidHom_apply, ← map_pow] at hz
      refine Subgroup.mem_sup.mpr ⟨g * (g' ^ n)⁻¹, ?_, g' ^ n, ⟨g', rfl⟩, inv_mul_cancel_right g (g' ^ n)⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hz, mul_inv_cancel]
  have h3 : ((powMonoidHom n : MonoidHom G G).range).relIndex (φ.ker ⊔ (powMonoidHom n : MonoidHom G G).range) =
      ((powMonoidHom n : MonoidHom G G).range ⊓ φ.ker).relIndex φ.ker := by
    rw [Subgroup.relIndex_sup_right, Subgroup.inf_relIndex_right]
  have h4 : (powMonoidHom n : MonoidHom G G).range ⊓ φ.ker = ((powMonoidHom n : MonoidHom U U).range).map ι := by
    apply le_antisymm
    ·
      intro x hx'
      obtain ⟨⟨g, rfl⟩, hx⟩ := Subgroup.mem_inf.mp hx'
      rw [MonoidHom.mem_ker, powMonoidHom_apply, map_pow] at hx
      have hg' : g ∈ ι.range := by
        rw [hexact]
        apply hF _ hx
      obtain ⟨u, rfl⟩ := hg'
      refine ⟨u ^ n, ⟨u, rfl⟩, by rw [map_pow, powMonoidHom_apply]⟩
    ·
      rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
      refine ⟨⟨ι u, by rw [powMonoidHom_apply, powMonoidHom_apply, map_pow]⟩, ?_⟩
      rw [← hexact]
      refine ⟨u ^ n, by rw [powMonoidHom_apply, map_pow]⟩
  have h5 : (((powMonoidHom n : MonoidHom U U).range).map ι).relIndex φ.ker =
      ((powMonoidHom n : MonoidHom U U).range).index := by
    rw [← hexact, MonoidHom.range_eq_map ι, ← Subgroup.relIndex_comap,
      Subgroup.comap_map_eq_self_of_injective hι, Subgroup.relIndex_top_right]
  calc
    _ = ((powMonoidHom n : MonoidHom G G).range).relIndex (φ.ker ⊔ (powMonoidHom n : MonoidHom G G).range) * (φ.ker ⊔ (powMonoidHom n : MonoidHom G G).range).index :=
      (Subgroup.relIndex_mul_index le_sup_right).symm
    _ = ((powMonoidHom n : MonoidHom G G).range ⊓ φ.ker).relIndex φ.ker * ((powMonoidHom n : MonoidHom F F).range).index := by
      rw [h3, h1, Subgroup.index_comap_of_surjective _ hφ]
    _ = (powMonoidHom n : MonoidHom F F).range.index * (powMonoidHom n : MonoidHom U U).range.index := by
      rw [h4, h5, mul_comm]


-- created on 2026-10-20
