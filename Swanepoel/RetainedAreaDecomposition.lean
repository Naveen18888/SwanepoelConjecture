module
public import Swanepoel.PentagonFaceArea
public import Swanepoel.RhombusFaceArea
public import Swanepoel.RetainedRhombusCounting
public import Swanepoel.QuadraticGeometryReduction
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem PennyGraph.sum_bounded_faces_partition {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (weight : PlaneFace G→ℝ) :
    (∑ F : BoundedFace G,weight (G.boundedFaceAsPlane F))=
      (∑ R : RhombusSet G,weight (G.boundedFaceAsPlane (rhombusFaceMap G ht R)))+
        ∑ F∈G.defectPlaneFaces ht,weight F := by
  have hp := Finset.sum_sdiff (f := fun F => weight (G.boundedFaceAsPlane F))
    (Finset.subset_univ (G.rhombicFaces ht))
  have hr : (∑ F∈G.rhombicFaces ht,weight (G.boundedFaceAsPlane F))=
      ∑ R : RhombusSet G,weight (G.boundedFaceAsPlane (rhombusFaceMap G ht R)) := by
    rw [PennyGraph.rhombicFaces,Finset.sum_image (fun R _ S _ h => rhombusFaceMap_injective G ht h)]
  have hd : (∑ F∈G.defectFaces ht,weight (G.boundedFaceAsPlane F))=
      ∑ F∈G.defectPlaneFaces ht,weight F := by
    change _=∑ F∈(G.defectFaces ht).image G.boundedFaceAsPlane,weight F
    rw [Finset.sum_image (fun F _ H _ h => G.boundedFaceAsPlane_injective h)]
  change (∑ F∈G.defectFaces ht,weight (G.boundedFaceAsPlane F))+
    (∑ F∈G.rhombicFaces ht,weight (G.boundedFaceAsPlane F))=_ at hp
  rw [hr,hd] at hp
  linarith

theorem PennyGraph.retained_area_decomposition {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    (P : Fin n→Plane)
    (hP : ∀ e : OrientedEdge G,P e.val.2-P e.val.1=retainedDisplacement (G.familyTrackComponents Y) e) :
    (∑ F : BoundedFace G,G.faceSignedArea P (G.boundedFaceAsPlane F))=
      (∑ R∈G.retainedRhombi (G.familyTrackComponents Y),
        G.faceSignedArea G.point (G.boundedFaceAsPlane (rhombusFaceMap G ht R)))+
        ∑ F∈Y,G.faceSignedArea G.point F := by
  rw [G.sum_bounded_faces_partition ht]
  congr 1
  · calc
      _ = ∑ R : RhombusSet G, if edgeComponent R.representative.edgeAB∈G.familyTrackComponents Y ∧
          edgeComponent R.representative.edgeAD∈G.familyTrackComponents Y then
          G.faceSignedArea G.point (G.boundedFaceAsPlane (rhombusFaceMap G ht R)) else 0 := by
        apply Finset.sum_congr rfl
        intro R _
        exact G.retained_rhombus_signed_area ht _ P hP _ R.representative rfl
      _ = _ := (Finset.sum_filter _ _).symm
  · calc
      _ = ∑ F∈Y,G.faceSignedArea P F := (Finset.sum_subset hY.subset_defects
          (fun F hF hnot => G.retained_unselected_defect_area ht hY P hP F hF hnot)).symm
      _ = _ := Finset.sum_congr rfl (fun F hF => G.retained_selected_defect_area ht hY P hP F hF)

theorem PennyGraph.retained_crossing_area_lower {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (Y : Finset (PlaneFace G)) :
    Real.sqrt 3/2*(G.familyInternalCrossings ht Y : ℝ)≤
      ∑ R∈G.retainedRhombi (G.familyTrackComponents Y),
        G.faceSignedArea G.point (G.boundedFaceAsPlane (rhombusFaceMap G ht R)) := by
  rw [← G.retained_family_rhombi_card ht Y]
  calc
    _ = ∑ _∈G.retainedRhombi (G.familyTrackComponents Y),Real.sqrt 3/2 := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun R _ => (R.representative.faceSignedArea_lower ht _ rfl).le)

def PennyGraph.DefectAreaLowerBound {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) : Prop :=
  ∀ F∈G.defectPlaneFaces ht,Real.sqrt 3/2≤G.faceSignedArea G.point F

theorem PennyGraph.defect_area_lower_of_large_faces {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (hlarge : ∀ F∈G.defectPlaneFaces ht,6≤(G.faceSourcePorts F).card →
      Real.sqrt 3/2≤G.faceSignedArea G.point F) : G.DefectAreaLowerBound ht := by
  intro F hF
  have hm := G.defect_source_ports_five_le ht F hF
  by_cases hfive : (G.faceSourcePorts F).card=5
  · exact (G.five_port_face_area_lower ht F hF hdegree hfive).le
  · exact hlarge F hF (by omega)

theorem PennyGraph.retained_area_lower_of_defect_area {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (hdefect : G.DefectAreaLowerBound ht) : G.RetainedAreaLowerBound ht := by
  intro Y hY P hP
  have hr := G.retained_crossing_area_lower ht Y
  have hf : Real.sqrt 3/2*(Y.card : ℝ)≤∑ F∈Y,G.faceSignedArea G.point F := by
    calc
      _ = ∑ _∈Y,Real.sqrt 3/2 := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun F hF => hdefect F (hY.subset_defects hF))
  rw [G.retained_area_decomposition ht hY P hP]
  unfold PennyGraph.familyR
  push_cast
  nlinarith

theorem PennyGraph.canonical_quadratic_bound_of_local_geometry {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (hdefect : G.DefectAreaLowerBound ht) (hpentagon : G.PentagonCrossingEstimate ht) :
    (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).QuadraticBound :=
  G.canonical_quadratic_bound_of_geometry ht hc hdegree (G.retained_area_lower_of_defect_area ht hdefect) hpentagon

end Swanepoel
