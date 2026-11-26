module
public import Swanepoel.L38HalfAreaFamilies
public import Swanepoel.L38HalfPentagonTracks
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

theorem bankDefectImage_tracks_image (ht : G.TriangleFree) (side : Bool)
    (Y : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side) :
    ((B.halfGraph side).familyTrackComponents (B.bankDefectImage ht side Y hY)).image (B.halfComponentMap side)=
      G.familyTrackComponents Y := by
  unfold PennyGraph.familyTrackComponents
  rw [Finset.image_image]
  change ((B.halfGraph side).familySourcePorts (B.bankDefectImage ht side Y hY)).image
    (edgeComponent ∘ B.halfEdge side)=(G.familySourcePorts Y).image edgeComponent
  rw [← Finset.image_image,B.bankDefectImage_sourcePorts_image ht side Y hY]

theorem bankDefectImage_tracks_map_injOn (ht : G.TriangleFree) (side : Bool)
    (Y : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side) :
    Set.InjOn (B.halfComponentMap side)
      ((B.halfGraph side).familyTrackComponents (B.bankDefectImage ht side Y hY) :
        Set (TrackComponent (B.halfGraph side))) := by
  intro c hc d hd hcomp
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hd
  have heOld : B.halfEdge side e∈G.familySourcePorts Y := by
    rw [← B.bankDefectImage_sourcePorts_image ht side Y hY]
    exact Finset.mem_image.mpr ⟨e,he,rfl⟩
  have hfOld : B.halfEdge side f∈G.familySourcePorts Y := by
    rw [← B.bankDefectImage_sourcePorts_image ht side Y hY]
    exact Finset.mem_image.mpr ⟨f,hf,rfl⟩
  have hep := (Finset.mem_filter.mp heOld).2
  have hfp := (Finset.mem_filter.mp hfOld).2
  rw [B.halfComponentMap_edge,B.halfComponentMap_edge] at hcomp
  exact B.half_old_source_components_eq ht side e f hep.1 hfp.1 (hY hep.2) (hY hfp.2) hcomp

theorem bankDefectImage_tracks_card (ht : G.TriangleFree) (side : Bool)
    (Y : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side) :
    ((B.halfGraph side).familyTrackComponents (B.bankDefectImage ht side Y hY)).card=
      (G.familyTrackComponents Y).card := by
  rw [← B.bankDefectImage_tracks_image ht side Y hY,
    Finset.card_image_of_injOn (B.bankDefectImage_tracks_map_injOn ht side Y hY)]

theorem bankDefectImage_K (ht : G.TriangleFree) (side : Bool)
    (Y : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side) :
    (B.halfGraph side).familyK (B.bankDefectImage ht side Y hY)=G.familyK Y := by
  unfold PennyGraph.familyK
  rw [B.bankDefectImage_tracks_card ht side Y hY,B.bankDefectImage_card ht side Y hY]

theorem bankDefectImage_unpaired_card (ht : G.TriangleFree) (side : Bool)
    (Y : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side) :
    ((B.halfGraph side).familyUnpairedPorts (B.bankDefectImage ht side Y hY)).card=
      (G.familyUnpairedPorts Y).card := by
  have hH := (B.halfGraph side).partial_family_endpoint_conservation (B.halfGraph_triangleFree ht side)
    (B.bankDefectImage ht side Y hY)
  have hG := G.partial_family_endpoint_conservation ht Y
  rw [B.bankDefectImage_tracks_card ht side Y hY,
    B.bankDefectImage_sourcePorts_card ht side Y hY] at hH
  omega

theorem bankDefectImage_boundary_count_of_joinClosed (ht : G.TriangleFree) (side : Bool)
    (Y : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side)
    (hclosed : (B.halfGraph side).IsJoinClosed (B.halfGraph_triangleFree ht side)
      (B.bankDefectImage ht side Y hY)) :
    (B.halfGraph side).familyBoundaryEndCount (B.bankDefectImage ht side Y hY)=
      (G.familyUnpairedPorts Y).card := by
  have hH := (B.halfGraph side).family_K_port_conservation (B.halfGraph_triangleFree ht side) hclosed
  have hG := G.partial_family_K_port_conservation ht Y
  rw [B.bankDefectImage_K ht side Y hY,B.bankDefectImage_portExcess ht side Y hY] at hH
  omega

end OrdinaryCutBanks
end Swanepoel
