module
public import Swanepoel.ConvexSourceTracks
public import Swanepoel.RetainedRhombusCounting
public import Swanepoel.JoinClosedPentagons
public import Swanepoel.SpineIntersections
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

namespace PentagonFaceBoundary
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} (P : PentagonFaceBoundary G F)
include P

theorem source_spines_disjoint (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht)
    (e f : OrientedEdge G) (he : e∈G.faceSourcePorts F) (hf : f∈G.faceSourcePorts F)
    (hne : edgeComponent e≠edgeComponent f) :
    Disjoint (trackSpineTrace (edgeComponent e)) (trackSpineTrace (edgeComponent f)) :=
  track_spines_disjoint_of_noncrossing ht hne (P.source_tracks_noncrossing ht hF e f he hf)

theorem internal_crossings_zero (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht) :
    G.familyInternalCrossings ht {F}=0 := by
  rw [← G.retained_family_rhombi_card ht {F}]
  have hempty : G.retainedRhombi (G.familyTrackComponents {F})=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro R hR
    have hR' := (Finset.mem_filter.mp hR).2
    change edgeComponent R.representative.edgeAB∈G.familyTrackComponents {F} ∧
      edgeComponent R.representative.edgeAD∈G.familyTrackComponents {F} at hR'
    rw [PennyGraph.familyTrackComponents,G.familySourcePorts_singleton] at hR'
    obtain ⟨e,he,heC⟩ := Finset.mem_image.mp hR'.1
    obtain ⟨f,hf,hfC⟩ := Finset.mem_image.mp hR'.2
    exact P.source_tracks_noncrossing ht hF e f he hf
      ⟨R.representative,Or.inl ⟨heC.symm,hfC.symm⟩⟩
  rw [hempty,Finset.card_empty]

end PentagonFaceBoundary

theorem PennyGraph.five_port_internal_crossings_zero {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (F : PlaneFace G) (hF : F∈G.defectPlaneFaces ht)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (hfive : (G.faceSourcePorts F).card=5) : G.familyInternalCrossings ht {F}=0 := by
  obtain ⟨P⟩ := G.five_port_face_boundary ht F hF hdegree hfive
  exact P.internal_crossings_zero ht hF

end Swanepoel
