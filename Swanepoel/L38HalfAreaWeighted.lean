module
public import Swanepoel.L38AreaCounts
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem PennyGraph.l38_weighted_area_lower_of_defect_area {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (hdefect : G.DefectAreaLowerBound ht)
    {Y Z : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) (hZ : G.IsJoinClosed ht Z)
    (P : Fin n→Plane)
    (hP : ∀ e : OrientedEdge G,P e.val.2-P e.val.1=trackDisplacement (G.l38TrackWeight Y Z) e) :
    Real.sqrt 3/2*(G.l38RhombusMass Y Z+G.l38DefectMass ht Y Z)≤
      ∑ F : BoundedFace G,G.faceSignedArea P (G.boundedFaceAsPlane F) := by
  rw [G.l38_weighted_area_decomposition ht hY hZ P hP]
  have hr : Real.sqrt 3/2*G.l38RhombusMass Y Z≤
      ∑ R : RhombusSet G,G.l38TrackWeight Y Z (edgeComponent R.representative.edgeAB)*
        G.l38TrackWeight Y Z (edgeComponent R.representative.edgeAD)*
        G.faceSignedArea G.point (G.boundedFaceAsPlane (rhombusFaceMap G ht R)) := by
    unfold PennyGraph.l38RhombusMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro R _
    have hw := mul_nonneg (G.l38TrackWeight_nonneg Y Z (edgeComponent R.representative.edgeAB))
      (G.l38TrackWeight_nonneg Y Z (edgeComponent R.representative.edgeAD))
    have harea := R.representative.faceSignedArea_lower ht
      (G.boundedFaceAsPlane (rhombusFaceMap G ht R)) rfl
    nlinarith only [mul_nonneg hw (sub_nonneg.mpr harea.le)]
  have hd : Real.sqrt 3/2*G.l38DefectMass ht Y Z≤
      ∑ F∈G.defectPlaneFaces ht,(G.l38FaceWeight Y Z F)^2*G.faceSignedArea G.point F := by
    unfold PennyGraph.l38DefectMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro F hF
    have harea := hdefect F hF
    nlinarith only [mul_nonneg (sq_nonneg (G.l38FaceWeight Y Z F)) (sub_nonneg.mpr harea)]
  nlinarith only [hr,hd]

theorem PennyGraph.l38_area_count_lower_of_defect_area {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (hdefect : G.DefectAreaLowerBound ht)
    {Y Z : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) (hZ : G.IsJoinClosed ht Z)
    (hYZ : Disjoint Y Z) (P : Fin n→Plane)
    (hP : ∀ e : OrientedEdge G,P e.val.2-P e.val.1=trackDisplacement (G.l38TrackWeight Y Z) e) :
    Real.sqrt 3/2*((G.familyInternalCrossings ht Y : ℝ)+Y.card+
      ((G.familyInternalCrossings ht Z : ℝ)+Z.card)/4+(G.interFamilyCrossings ht Y Z : ℝ)/2)≤
      ∑ F : BoundedFace G,G.faceSignedArea P (G.boundedFaceAsPlane F) := by
  have h := G.l38_weighted_area_lower_of_defect_area ht hdefect hY hZ P hP
  rw [G.l38RhombusMass_counts ht hY hZ hYZ,G.l38DefectMass_counts ht hY hZ hYZ] at h
  convert h using 1
  ring

theorem PennyGraph.exists_l38_area_count_lower_of_defect_area {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (hc : G.graph.Connected) (hdefect : G.DefectAreaLowerBound ht)
    {Y Z : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) (hZ : G.IsJoinClosed ht Z)
    (hYZ : Disjoint Y Z) :
    ∃ P : Fin n→Plane,(∀ e : OrientedEdge G,P e.val.2-P e.val.1=trackDisplacement (G.l38TrackWeight Y Z) e) ∧
      Real.sqrt 3/2*((G.familyInternalCrossings ht Y : ℝ)+Y.card+
        ((G.familyInternalCrossings ht Z : ℝ)+Z.card)/4+(G.interFamilyCrossings ht Y Z : ℝ)/2)≤
        ∑ F : BoundedFace G,G.faceSignedArea P (G.boundedFaceAsPlane F) := by
  obtain ⟨P,hP⟩ := G.exists_l38_weighted_potential ht hc hY hZ
  exact ⟨P,hP,G.l38_area_count_lower_of_defect_area ht hdefect hY hZ hYZ P hP⟩

end Swanepoel
