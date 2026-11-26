module
public import Swanepoel.L38HalfAreaConverse
public import Swanepoel.L38HalfAreaFamilyTracks
public import Swanepoel.L38HalfAreaPerimeter
public import Swanepoel.L38HalfPentagonIsolation
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

def halfIsolatedDefects (ht : G.TriangleFree) (side : Bool) : Finset (PlaneFace (B.halfGraph side)) :=
  B.bankDefectImage ht side (B.isolatedTwoPortPentagons ht side) (Finset.filter_subset _ _)

def halfRemainderDefects (ht : G.TriangleFree) (side : Bool) : Finset (PlaneFace (B.halfGraph side)) :=
  B.bankDefectImage ht side (B.bankRemainder ht side) (B.bankRemainder_subset ht side)

theorem halfIsolatedDefects_joinClosed (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool) :
    (B.halfGraph side).IsJoinClosed (B.halfGraph_triangleFree ht side) (B.halfIsolatedDefects ht side) := by
  refine ⟨B.bankDefectImage_subset_defects ht side _ _,?_⟩
  intro e f he hf hcomp heS hfDef
  have hePort : e∈(B.halfGraph side).familySourcePorts (B.halfIsolatedDefects ht side) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,he,heS⟩
  have heOld : B.halfEdge side e∈G.familySourcePorts (B.isolatedTwoPortPentagons ht side) := by
    rw [← B.bankDefectImage_sourcePorts_image ht side (B.isolatedTwoPortPentagons ht side)
      (Finset.filter_subset _ _)]
    exact Finset.mem_image.mpr ⟨e,hePort,rfl⟩
  have heFree := B.isolated_sourcePorts_subset_unpaired ht side heOld
  have hfe := B.half_unpaired_bounded_source_unique ht side
    (B.half_defect_bank_face_surjective ht hc hcut side) e f heFree hfDef hcomp.symm
  simpa only [hfe] using heS

theorem halfRemainderDefects_eq_sdiff (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool) :
    B.halfRemainderDefects ht side=
      (B.halfGraph side).defectPlaneFaces (B.halfGraph_triangleFree ht side)\B.halfIsolatedDefects ht side := by
  ext K
  constructor
  · intro hK
    have hDef := B.bankDefectImage_subset_defects ht side (B.bankRemainder ht side)
      (B.bankRemainder_subset ht side) hK
    have hDis := B.bankDefectImage_disjoint ht side (B.isolatedTwoPortPentagons ht side)
      (B.bankRemainder ht side) (Finset.filter_subset _ _) (B.bankRemainder_subset ht side)
      (B.bank_isolated_remainder_disjoint ht side)
    exact Finset.mem_sdiff.mpr ⟨hDef,fun hiso => Finset.disjoint_left.mp hDis hiso hK⟩
  · intro hK
    have hKD := Finset.mem_sdiff.mp hK
    obtain ⟨F,hF,hmap⟩ := B.half_defect_bank_face_surjective ht hc hcut side K hKD.1
    have hnot : F∉B.isolatedTwoPortPentagons ht side := by
      intro hFS
      apply hKD.2
      have hm := B.bankDefectImage_mem ht side (B.isolatedTwoPortPentagons ht side)
        (Finset.filter_subset _ _) F hFS
      simpa only [halfIsolatedDefects,hmap] using hm
    have hRest : F∈B.bankRemainder ht side := Finset.mem_sdiff.mpr ⟨hF,hnot⟩
    have hm := B.bankDefectImage_mem ht side (B.bankRemainder ht side)
      (B.bankRemainder_subset ht side) F hRest
    simpa only [halfRemainderDefects,hmap] using hm

theorem halfRemainderDefects_joinClosed (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool) :
    (B.halfGraph side).IsJoinClosed (B.halfGraph_triangleFree ht side) (B.halfRemainderDefects ht side) := by
  rw [B.halfRemainderDefects_eq_sdiff ht hc hcut side]
  exact ((B.halfGraph side).joinClosed_all_defects (B.halfGraph_triangleFree ht side)).sdiff
    (B.halfIsolatedDefects_joinClosed ht hc hcut side)

theorem half_isolated_ports_boundary (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool)
    (F : PlaneFace (B.halfGraph side)) (hF : F∈B.halfIsolatedDefects ht side) :
    ∀ e∈(B.halfGraph side).faceSourcePorts F,
      edgeComponent e∈(B.halfGraph side).familyBoundaryTrackComponents
        ((B.halfGraph side).defectPlaneFaces (B.halfGraph_triangleFree ht side)) := by
  obtain ⟨K,_,rfl⟩ := Finset.mem_image.mp hF
  exact B.isolated_pentagon_half_boundary_ports ht side
    (B.half_defect_bank_face_surjective ht hc hcut side) K.val K.property

theorem half_isolated_other_source_unbounded (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool)
    (F : PlaneFace (B.halfGraph side)) (hF : F∈B.halfIsolatedDefects ht side)
    {e f : OrientedEdge (B.halfGraph side)} (he : e∈(B.halfGraph side).faceSourcePorts F)
    (hf : SpineSource f) (hcomp : edgeComponent e=edgeComponent f) (hne : f≠e) :
    ¬Bornology.IsBounded ((B.halfGraph side).sourceFace f).val :=
  (B.halfGraph side).boundary_face_other_source_end_unbounded (B.halfGraph_triangleFree ht side)
    ((B.halfGraph side).joinClosed_all_defects (B.halfGraph_triangleFree ht side)) F
    (B.bankDefectImage_subset_defects ht side _ _ hF)
    (B.half_isolated_ports_boundary ht hc hcut side F hF) he hf hcomp hne

theorem halfIsolatedDefects_boundary_count (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool) :
    (B.halfGraph side).familyBoundaryEndCount (B.halfIsolatedDefects ht side)=
      5*(B.isolatedTwoPortPentagons ht side).card := by
  have hb := B.bankDefectImage_boundary_count_of_joinClosed ht side
    (B.isolatedTwoPortPentagons ht side) (Finset.filter_subset _ _)
    (B.halfIsolatedDefects_joinClosed ht hc hcut side)
  have htS := B.isolated_track_count ht side
  have hinj := (G.familyUnpairedPorts_component_injOn (B.bankDefectFamily ht side)).mono
    (B.isolated_sourcePorts_subset_unpaired ht side)
  have hSrc : (G.familySourcePorts (B.isolatedTwoPortPentagons ht side)).card=
      (G.familyTrackComponents (B.isolatedTwoPortPentagons ht side)).card :=
    (Finset.card_image_of_injOn hinj).symm
  have he := G.partial_family_endpoint_conservation ht (B.isolatedTwoPortPentagons ht side)
  change (B.halfGraph side).familyBoundaryEndCount
    (B.bankDefectImage ht side (B.isolatedTwoPortPentagons ht side) (Finset.filter_subset _ _))=_
  omega

theorem halfRemainderDefects_boundary_count (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool) :
    ((B.halfGraph side).familyBoundaryEndCount (B.halfRemainderDefects ht side) : ℤ)=
      2*G.familyK (B.bankRemainder ht side)-G.familyPortExcess (B.bankRemainder ht side) := by
  have hb := B.bankDefectImage_boundary_count_of_joinClosed ht side
    (B.bankRemainder ht side) (B.bankRemainder_subset ht side)
    (B.halfRemainderDefects_joinClosed ht hc hcut side)
  have he := G.partial_family_K_port_conservation ht (B.bankRemainder ht side)
  change ((B.halfGraph side).familyBoundaryEndCount
    (B.bankDefectImage ht side (B.bankRemainder ht side) (B.bankRemainder_subset ht side)) : ℤ)=_
  omega

theorem half_weighted_outer_perimeter_eq (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool)
    (P : Fin (B.bankVertices side).card→Plane)
    (hP : ∀ e : OrientedEdge (B.halfGraph side),P e.val.2-P e.val.1=
      trackDisplacement ((B.halfGraph side).l38TrackWeight
        (B.halfRemainderDefects ht side) (B.halfIsolatedDefects ht side)) e)
    (outer : PlaneFace (B.halfGraph side)) (houter : ¬Bornology.IsBounded outer.val) :
    (∑ e∈(B.halfGraph side).faceIncidentDarts outer,‖P e.val.2-P e.val.1‖)=
      (5/2:ℝ)*(B.isolatedTwoPortPentagons ht side).card+
        2*(G.familyK (B.bankRemainder ht side) : ℝ)-(G.familyPortExcess (B.bankRemainder ht side) : ℝ) := by
  have hp := (B.halfGraph side).l38_outer_perimeter_eq (B.halfGraph_triangleFree ht side)
    (B.halfRemainderDefects ht side) (B.halfIsolatedDefects ht side) P hP outer houter
  have hS : ((B.halfGraph side).familyBoundaryEndCount (B.halfIsolatedDefects ht side) : ℝ)=
      5*(B.isolatedTwoPortPentagons ht side).card := by
    exact_mod_cast B.halfIsolatedDefects_boundary_count ht hc hcut side
  have hY : ((B.halfGraph side).familyBoundaryEndCount (B.halfRemainderDefects ht side) : ℝ)=
      2*(G.familyK (B.bankRemainder ht side) : ℝ)-(G.familyPortExcess (B.bankRemainder ht side) : ℝ) := by
    exact_mod_cast B.halfRemainderDefects_boundary_count ht hc hcut side
  rw [hp,hS,hY]
  ring

end OrdinaryCutBanks
end Swanepoel
