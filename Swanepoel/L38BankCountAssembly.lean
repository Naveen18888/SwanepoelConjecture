module
public import Swanepoel.L38BankPartition
public import Swanepoel.L38BankCrossingRealization
public import Swanepoel.PentagonRemovalAccounting
@[expose] public section
set_option autoImplicit false

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem PennyGraph.familyTrackIndices_disjoint_of_components {n : ℕ} (G : PennyGraph n)
    (Y Z : Finset (PlaneFace G))
    (hYZ : Disjoint (G.familyTrackComponents Y) (G.familyTrackComponents Z)) :
    Disjoint (G.familyTrackIndices Y) (G.familyTrackIndices Z) := by
  apply Finset.disjoint_left.mpr
  intro i hiY hiZ
  obtain ⟨c,hc,hci⟩ := Finset.mem_map.mp hiY
  obtain ⟨d,hd,hdi⟩ := Finset.mem_map.mp hiZ
  have hcd : c=d := (Fintype.equivFin (TrackComponent G)).injective (hci.trans hdi.symm)
  exact Finset.disjoint_left.mp hYZ (hcd ▸ hc) hd

theorem PennyGraph.family_internal_union_of_components {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (Y Z : Finset (PlaneFace G))
    (hYZ : Disjoint (G.familyTrackComponents Y) (G.familyTrackComponents Z)) :
    G.familyInternalCrossings ht (Y∪Z)=G.familyInternalCrossings ht Y+
      G.familyInternalCrossings ht Z+G.interFamilyCrossings ht Y Z := by
  unfold PennyGraph.familyInternalCrossings PennyGraph.interFamilyCrossings
  rw [G.familyTrackIndices_union]
  exact TrackSystem.internal_union _ _ _ (G.familyTrackIndices_disjoint_of_components Y Z hYZ)

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

theorem bank_weighted_count_split (ht : G.TriangleFree) (side : Bool) :
    G.familyR ht (B.bankDefectFamily ht side)=
      ((G.familyInternalCrossings ht (B.isolatedTwoPortPentagons ht side) : ℤ)+
        (B.isolatedTwoPortPentagons ht side).card)+
      (G.interFamilyCrossings ht (B.isolatedTwoPortPentagons ht side) (B.bankRemainder ht side) : ℤ)+
      ((G.familyInternalCrossings ht (B.bankRemainder ht side) : ℤ)+(B.bankRemainder ht side).card) := by
  have hU := B.bank_isolated_remainder_union ht side
  have hcross := G.family_internal_union_of_components ht
    (B.isolatedTwoPortPentagons ht side) (B.bankRemainder ht side)
    (B.isolated_remainder_tracks_disjoint ht side)
  have hcard := Finset.card_union_of_disjoint (B.bank_isolated_remainder_disjoint ht side)
  rw [hU] at hcross hcard
  unfold PennyGraph.familyR
  rw [hcross,hcard]
  push_cast
  ring

end OrdinaryCutBanks
end Swanepoel
