import Mathlib

namespace FixedPoints

variable {S : Type*} [CommRing S] {G : Type*} [Group G] [MulSemiringAction G S]
  [FaithfulSMul G S]

theorem isGaloisGroup_subring : IsGaloisGroup G (FixedPoints.subring S G) S where
  faithful := inferInstance
  commutes := ⟨fun g r s => by
    show g • ((r : S) * s) = (r : S) * (g • s); rw [smul_mul', r.2 g]⟩
  isInvariant := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩

end FixedPoints

/--
info: 'FixedPoints.isGaloisGroup_subring' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FixedPoints.isGaloisGroup_subring
