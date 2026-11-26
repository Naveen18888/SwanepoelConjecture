module
public import Swanepoel.FaceBoundaryPermutation
public import Swanepoel.JoinClosedDecomposition
public import Swanepoel.RhombusDisplacementPotential
public import Swanepoel.FaceDualConnectivityLinear
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem PennyGraph.face_incident_gradient_sum {n : ℕ} (G : PennyGraph n)
    (F : PlaneFace G) (P : Fin n → Plane) :
    (∑ e∈G.faceIncidentDarts F, (P e.val.2-P e.val.1))=0 := by
  have h := G.sum_faceBoundaryPredecessor F (fun e => P e.val.2)
  simp only [G.faceBoundaryPredecessor_end] at h
  rw [Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr h.symm

theorem PennyGraph.face_displacement_sum_of_local_potential {n : ℕ} (G : PennyGraph n)
    (A : Finset (TrackComponent G)) (F : PlaneFace G) (P : Fin n → Plane)
    (hP : ∀ e∈G.faceIncidentDarts F, P e.val.2-P e.val.1=retainedDisplacement A e) :
    (∑ e∈G.faceIncidentDarts F, retainedDisplacement A e)=0 := by
  calc
    _ = ∑ e∈G.faceIncidentDarts F, (P e.val.2-P e.val.1) := by
      apply Finset.sum_congr rfl
      intro e he
      exact (hP e he).symm
    _ = 0 := G.face_incident_gradient_sum F P

theorem RhombusCell.incident_edge_endpoints {n : ℕ} {G : PennyGraph n}
    (C : RhombusCell G) (ht : G.TriangleFree) (e : OrientedEdge G)
    (hface : (G.sourceFace e).val=C.openRegion) :
    e.val.1∈C.corners ∧ e.val.2∈C.corners := by
  have hcl := G.edge_midpoint_mem_closure_sourceFace e
  rw [hface] at hcl
  have hnot : G.edgePoint e.val.1 e.val.2 (1/2)∉C.openRegion := by
    intro hz
    exact C.openRegion_subset_complement ht hz (G.edgeTrace_subset_drawing _ _ e.property
      ⟨1/2,⟨by norm_num,by norm_num⟩,rfl⟩)
  have hboundary := (C.closedRegion_subset_open_union_boundary ht
    (C.closure_openRegion_subset hcl)).resolve_left hnot
  obtain ⟨D,hcorners,he⟩ := C.align_edge_of_midpoint_mem_boundary e hboundary
  rw [he,← hcorners]
  constructor <;> simp [RhombusCell.corners]

theorem PennyGraph.rhombus_face_retained_displacement_sum {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (A : Finset (TrackComponent G)) (F : PlaneFace G)
    (C : RhombusCell G) (hface : F.val=C.openRegion) :
    (∑ e∈G.faceIncidentDarts F, retainedDisplacement A e)=0 := by
  let w (c : TrackComponent G) : ℝ := if c∈A then 1 else 0
  apply G.face_displacement_sum_of_local_potential A F (C.displacementVertexMap w)
  intro e he
  have heF : G.sourceFace e=F := (Finset.mem_filter.mp he).2
  have hC : (G.sourceFace e).val=C.openRegion :=
    (congrArg Subtype.val heF).trans hface
  obtain ⟨ha,hb⟩ := C.incident_edge_endpoints ht e hC
  exact C.displacementVertexMap_edge ht w e ha hb

theorem PennyGraph.family_displacement_on_unretained_defect {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    (F : PlaneFace G) (hF : F∈G.defectPlaneFaces ht) (hnot : F∉Y)
    (e : OrientedEdge G) (heF : G.sourceFace e=F) :
    retainedDisplacement (G.familyTrackComponents Y) e=0 := by
  apply retainedDisplacement_of_notMem
  intro hm
  obtain ⟨f,hf,hfe⟩ := Finset.mem_image.mp hm
  have hfs := (Finset.mem_filter.mp hf).2
  have hes : SpineSource e := G.spineSource_of_sourceFace_mem_defects ht e (heF ▸ hF)
  have heY := hY.other_bounded_end f e hfs.1 hes hfe hfs.2 (heF ▸ hF)
  exact hnot (heF ▸ heY)

theorem PennyGraph.defect_face_family_displacement_sum {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    (F : PlaneFace G) (hF : F∈G.defectPlaneFaces ht) :
    (∑ e∈G.faceIncidentDarts F, retainedDisplacement (G.familyTrackComponents Y) e)=0 := by
  by_cases hFY : F∈Y
  · calc
      _ = ∑ e∈G.faceIncidentDarts F, carriedVector e := by
        apply Finset.sum_congr rfl
        intro e he
        have heF := (Finset.mem_filter.mp he).2
        exact retainedDisplacement_of_mem _ e
          (G.familyTrackComponents_contains_face_edge ht hY e (heF ▸ hFY))
      _ = 0 := G.face_incident_carried_sum F
  · apply Finset.sum_eq_zero
    intro e he
    exact G.family_displacement_on_unretained_defect ht hY F hF hFY e
      (Finset.mem_filter.mp he).2

theorem PennyGraph.bounded_face_family_displacement_sum {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    (F : BoundedFace G) :
    (∑ e∈G.faceIncidentDarts (G.boundedFaceAsPlane F),
      retainedDisplacement (G.familyTrackComponents Y) e)=0 := by
  by_cases hR : F∈G.rhombicFaces ht
  · obtain ⟨R,_,hRF⟩ := Finset.mem_image.mp hR
    apply G.rhombus_face_retained_displacement_sum ht _ _ R.representative
    exact (congrArg Subtype.val hRF).symm
  · apply G.defect_face_family_displacement_sum ht hY
    apply Finset.mem_image.mpr
    exact ⟨F,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hR⟩,rfl⟩

end Swanepoel
