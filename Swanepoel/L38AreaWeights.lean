module
public import Swanepoel.Lemma37
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def PennyGraph.l38TrackWeight {n : ℕ} (G : PennyGraph n)
    (Y Z : Finset (PlaneFace G)) (c : TrackComponent G) : ℝ :=
  (if c∈G.familyTrackComponents Y then 1 else 0)+
    (if c∈G.familyTrackComponents Z then 1/2 else 0)

def PennyGraph.l38FaceWeight {n : ℕ} (G : PennyGraph n)
    (Y Z : Finset (PlaneFace G)) (F : PlaneFace G) : ℝ :=
  (if F∈Y then 1 else 0)+(if F∈Z then 1/2 else 0)

theorem PennyGraph.l38TrackWeight_nonneg {n : ℕ} (G : PennyGraph n)
    (Y Z : Finset (PlaneFace G)) (c : TrackComponent G) : 0≤G.l38TrackWeight Y Z c := by
  unfold l38TrackWeight
  split_ifs <;> norm_num

theorem PennyGraph.family_component_on_defect_iff {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    (F : PlaneFace G) (hF : F∈G.defectPlaneFaces ht) (e : OrientedEdge G)
    (he : G.sourceFace e=F) : edgeComponent e∈G.familyTrackComponents Y ↔ F∈Y := by
  constructor
  · intro hm
    obtain ⟨f,hf,hfe⟩ := Finset.mem_image.mp hm
    have hfs := (Finset.mem_filter.mp hf).2
    have hes := G.spineSource_of_sourceFace_mem_defects ht e (he ▸ hF)
    have heY := hY.other_bounded_end f e hfs.1 hes hfe hfs.2 (he ▸ hF)
    exact he ▸ heY
  · intro hFY
    exact G.familyTrackComponents_contains_face_edge ht hY e (he ▸ hFY)

theorem PennyGraph.l38TrackWeight_on_defect {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y Z : Finset (PlaneFace G)}
    (hY : G.IsJoinClosed ht Y) (hZ : G.IsJoinClosed ht Z)
    (F : PlaneFace G) (hF : F∈G.defectPlaneFaces ht) (e : OrientedEdge G)
    (he : G.sourceFace e=F) : G.l38TrackWeight Y Z (edgeComponent e)=G.l38FaceWeight Y Z F := by
  simp only [l38TrackWeight,l38FaceWeight,
    G.family_component_on_defect_iff ht hY F hF e he,
    G.family_component_on_defect_iff ht hZ F hF e he]

theorem PennyGraph.exists_l38_weighted_potential {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (hc : G.graph.Connected) {Y Z : Finset (PlaneFace G)}
    (hY : G.IsJoinClosed ht Y) (hZ : G.IsJoinClosed ht Z) :
    ∃ P : Fin n→Plane,∀ e : OrientedEdge G,
      P e.val.2-P e.val.1=trackDisplacement (G.l38TrackWeight Y Z) e := by
  obtain ⟨P,hP⟩ := G.exists_family_displacement_potential ht hY hc
  obtain ⟨Q,hQ⟩ := G.exists_family_displacement_potential ht hZ hc
  refine ⟨fun v => P v+(1/2:ℝ) • Q v,?_⟩
  intro e
  rw [show (P e.val.2+(1/2:ℝ) • Q e.val.2)-(P e.val.1+(1/2:ℝ) • Q e.val.1)=
    (P e.val.2-P e.val.1)+(1/2:ℝ) • (Q e.val.2-Q e.val.1) by module,hP,hQ]
  unfold retainedDisplacement trackDisplacement l38TrackWeight
  split_ifs <;> simp_all only [ite_true,ite_false] <;> module

theorem PennyGraph.faceSignedArea_smul {n : ℕ} (G : PennyGraph n)
    (P : Fin n→Plane) (F : PlaneFace G) (a : ℝ) :
    G.faceSignedArea (fun v => a • P v) F=a^2*G.faceSignedArea P F := by
  have hcross (v w : Fin n) : cross2 (a • P v) (a • P w)=a^2*cross2 (P v) (P w) := by
    rw [cross2_smul_left,cross2_smul_right]
    ring
  unfold faceSignedArea
  simp_rw [hcross]
  rw [← Finset.mul_sum]
  ring

theorem PennyGraph.weighted_defect_signed_area {n : ℕ} (G : PennyGraph n)
    (w : TrackComponent G→ℝ) (P : Fin n→Plane)
    (hP : ∀ e : OrientedEdge G,P e.val.2-P e.val.1=trackDisplacement w e)
    (F : PlaneFace G) (a : ℝ)
    (hweight : ∀ e∈G.faceIncidentDarts F,w (edgeComponent e)=a) :
    G.faceSignedArea P F=a^2*G.faceSignedArea G.point F := by
  have heq : G.faceSignedArea P F=G.faceSignedArea (fun v => a • G.point v) F := by
    apply G.faceSignedArea_eq_of_edge_differences
    intro e he
    rw [hP,trackDisplacement,hweight e he,← smul_sub]
    rfl
  rw [heq,G.faceSignedArea_smul]

theorem PennyGraph.weighted_rhombus_signed_area {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (w : TrackComponent G→ℝ) (P : Fin n→Plane)
    (hP : ∀ e : OrientedEdge G,P e.val.2-P e.val.1=trackDisplacement w e)
    (F : PlaneFace G) (C : RhombusCell G) (hface : F.val=C.openRegion) :
    G.faceSignedArea P F=w (edgeComponent C.edgeAB)*w (edgeComponent C.edgeAD)*G.faceSignedArea G.point F := by
  let L := C.displacementLinear w
  have heq : G.faceSignedArea P F=G.faceSignedArea (fun v => L (G.point v)) F := by
    apply G.faceSignedArea_eq_of_edge_differences
    intro e he
    rw [hP,← map_sub]
    have heF := (Finset.mem_filter.mp he).2
    obtain ⟨ha,hb⟩ := C.incident_edge_endpoints ht e ((congrArg Subtype.val heF).trans hface)
    exact (C.displacementLinear_on_inside_edge ht w e ha hb).symm
  rw [heq]
  unfold faceSignedArea
  simp_rw [show ∀ a b,cross2 (L (G.point a)) (L (G.point b))=
    w (edgeComponent C.edgeAB)*w (edgeComponent C.edgeAD)*cross2 (G.point a) (G.point b)
    from fun a b => C.displacementLinear_cross ht w _ _]
  rw [← Finset.mul_sum]
  ring

def PennyGraph.l38RhombusMass {n : ℕ} (G : PennyGraph n) (Y Z : Finset (PlaneFace G)) : ℝ :=
  ∑ R : RhombusSet G,G.l38TrackWeight Y Z (edgeComponent R.representative.edgeAB)*
    G.l38TrackWeight Y Z (edgeComponent R.representative.edgeAD)

def PennyGraph.l38DefectMass {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (Y Z : Finset (PlaneFace G)) : ℝ :=
  ∑ F∈G.defectPlaneFaces ht,(G.l38FaceWeight Y Z F)^2

theorem PennyGraph.l38_weighted_area_decomposition {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y Z : Finset (PlaneFace G)}
    (hY : G.IsJoinClosed ht Y) (hZ : G.IsJoinClosed ht Z) (P : Fin n→Plane)
    (hP : ∀ e : OrientedEdge G,P e.val.2-P e.val.1=trackDisplacement (G.l38TrackWeight Y Z) e) :
    (∑ F : BoundedFace G,G.faceSignedArea P (G.boundedFaceAsPlane F))=
      (∑ R : RhombusSet G,G.l38TrackWeight Y Z (edgeComponent R.representative.edgeAB)*
        G.l38TrackWeight Y Z (edgeComponent R.representative.edgeAD)*
        G.faceSignedArea G.point (G.boundedFaceAsPlane (rhombusFaceMap G ht R)))+
      ∑ F∈G.defectPlaneFaces ht,(G.l38FaceWeight Y Z F)^2*G.faceSignedArea G.point F := by
  rw [G.sum_bounded_faces_partition ht]
  congr 1
  · apply Finset.sum_congr rfl
    intro R _
    exact G.weighted_rhombus_signed_area ht _ P hP _ R.representative rfl
  · apply Finset.sum_congr rfl
    intro F hF
    apply G.weighted_defect_signed_area _ P hP F (G.l38FaceWeight Y Z F)
    intro e he
    exact G.l38TrackWeight_on_defect ht hY hZ F hF e (Finset.mem_filter.mp he).2

theorem PennyGraph.l38_weighted_area_lower {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
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
    unfold l38RhombusMass
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
    unfold l38DefectMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro F hF
    have harea := G.defect_area_lower ht hdegree F hF
    nlinarith only [mul_nonneg (sq_nonneg (G.l38FaceWeight Y Z F)) (sub_nonneg.mpr harea)]
  nlinarith only [hr,hd]

end Swanepoel
