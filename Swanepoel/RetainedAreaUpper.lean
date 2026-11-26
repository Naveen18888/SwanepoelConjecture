module
public import Swanepoel.FaceAreaIsoperimetry
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem PennyGraph.spineSource_of_sourceFace_unbounded {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (e : OrientedEdge G)
    (houter : ¬Bornology.IsBounded (G.sourceFace e).val) : SpineSource e := by
  by_contra hs
  obtain ⟨C,hC⟩ := (G.sourceFace_rhombic_iff_not_source ht e).mpr hs
  exact houter (hC.symm ▸ (C.isBoundedFace ht).2)

theorem PennyGraph.retained_outer_darts_eq {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (Y : Finset (PlaneFace G)) (outer : PlaneFace G)
    (houter : ¬Bornology.IsBounded outer.val) :
    (G.faceIncidentDarts outer).filter (fun e => edgeComponent e∈G.familyTrackComponents Y)=
      G.familyOuterSourceEnds Y := by
  obtain ⟨O,hO,hunique⟩ := G.exists_unique_outer_face
  have hOO : outer=O := hunique outer houter
  ext e
  constructor
  · intro he
    have he' := Finset.mem_filter.mp he
    have heF := (Finset.mem_filter.mp he'.1).2
    have heout : ¬Bornology.IsBounded (G.sourceFace e).val := heF ▸ houter
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,G.spineSource_of_sourceFace_unbounded ht e heout,he'.2⟩,heout⟩
  · intro he
    have he' := Finset.mem_filter.mp he
    have heS := (Finset.mem_filter.mp he'.1).2
    have heF : G.sourceFace e=outer := (hunique _ he'.2).trans hOO.symm
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,heF⟩,heS.2⟩

theorem retained_displacement_zero_or_unit {n : ℕ} {G : PennyGraph n}
    (A : Finset (TrackComponent G)) (e : OrientedEdge G) :
    retainedDisplacement A e=0 ∨ ‖retainedDisplacement A e‖=1 := by
  by_cases he : edgeComponent e∈A
  · right
    rw [retainedDisplacement_of_mem A e he,carriedVector_norm]
  · exact Or.inl (retainedDisplacement_of_notMem A e he)

theorem PennyGraph.retained_outer_perimeter_eq {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (Y : Finset (PlaneFace G)) (P : Fin n→Plane)
    (hP : ∀ e : OrientedEdge G,P e.val.2-P e.val.1=retainedDisplacement (G.familyTrackComponents Y) e)
    (outer : PlaneFace G) (houter : ¬Bornology.IsBounded outer.val) :
    (∑ e∈G.faceIncidentDarts outer,‖P e.val.2-P e.val.1‖)=(G.familyBoundaryEndCount Y : ℝ) := by
  have hn (e : OrientedEdge G) : ‖P e.val.2-P e.val.1‖=
      if edgeComponent e∈G.familyTrackComponents Y then (1:ℝ) else 0 := by
    rw [hP]
    by_cases he : edgeComponent e∈G.familyTrackComponents Y
    · rw [ite_eq_left he,retainedDisplacement_of_mem _ e he,carriedVector_norm]
    · rw [ite_eq_right he,retainedDisplacement_of_notMem _ e he,norm_zero]
  simp_rw [hn]
  rw [← Finset.sum_filter]
  rw [G.retained_outer_darts_eq ht Y outer houter]
  simp [PennyGraph.familyBoundaryEndCount]

theorem PennyGraph.retained_bounded_area_upper {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (Y : Finset (PlaneFace G)) (P : Fin n→Plane)
    (hP : ∀ e : OrientedEdge G,P e.val.2-P e.val.1=retainedDisplacement (G.familyTrackComponents Y) e) :
    (∑ F : BoundedFace G,G.faceSignedArea P (G.boundedFaceAsPlane F))≤
      (G.familyBoundaryEndCount Y : ℝ)^2/(4*Real.pi) := by
  obtain ⟨outer,houter,_⟩ := G.exists_unique_outer_face
  have hunit (e : OrientedEdge G) : P e.val.2-P e.val.1=0 ∨ ‖P e.val.2-P e.val.1‖=1 := by
    rw [hP]
    exact retained_displacement_zero_or_unit _ e
  have hupper := G.face_signed_area_perimeter_bound P hunit outer
  rw [G.retained_outer_perimeter_eq ht Y P hP outer houter] at hupper
  rw [G.bounded_face_signed_area_sum P outer houter]
  exact (neg_le_abs _).trans hupper

theorem PennyGraph.exists_retained_area_upper {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    (hc : G.graph.Connected) : ∃ P : Fin n→Plane,
      (∀ e : OrientedEdge G,P e.val.2-P e.val.1=retainedDisplacement (G.familyTrackComponents Y) e) ∧
      (∑ F : BoundedFace G,G.faceSignedArea P (G.boundedFaceAsPlane F))≤
        (G.familyBoundaryEndCount Y : ℝ)^2/(4*Real.pi) := by
  obtain ⟨P,hP⟩ := G.exists_family_displacement_potential ht hY hc
  exact ⟨P,hP,G.retained_bounded_area_upper ht Y P hP⟩

end Swanepoel
