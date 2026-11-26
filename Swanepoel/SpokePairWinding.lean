module
public import Swanepoel.SpokePairLoops
@[expose] public section

noncomputable section
namespace Swanepoel
open Set
attribute [local instance] Classical.propDecidable

abbrev PennyGraph.SpokePairSupport {n : ℕ} (G : PennyGraph n) (c d : TrackComponent G)
    (F outer : PlaneFace G) {a : Plane} (loop : PlaneChain a a) : Prop :=
  loop.trace⊆((trackSpineTrace c∪trackSpineTrace d)∪F.val)∪outer.val

theorem PennyGraph.trackSpine_preconnected {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (c : TrackComponent G) : IsPreconnected (trackSpineTrace c) := by
  obtain ⟨s,t,hs,htop,hE,_⟩ := component_spine_iff ht c.out
  have hsc : edgeComponent s=c := (positive_path_component hE.1).trans (Quotient.out_eq c)
  obtain ⟨p⟩ := PositiveSpineChain.exists_of_reach (hE.1.trans hE.2)
  have hp := p.complete_trace ht hs htop
  rw [hsc] at hp
  rw [← hp]
  exact p.toPlane.trace_preconnected

namespace PennyGraph.SpokePairSupport
variable {n : ℕ} {G : PennyGraph n} {c d : TrackComponent G} {F outer : PlaneFace G}
    {a : Plane} {loop : PlaneChain a a} (hloop : G.SpokePairSupport c d F outer loop)
include hloop

theorem vertex_not_on_loop (ht : G.TriangleFree) (i : Fin n) : G.point i∉loop.trace := by
  intro hi
  rcases hloop hi with ((hc | hd) | hF) | hO
  · exact G.vertex_not_on_track_spine ht c i hc
  · exact G.vertex_not_on_track_spine ht d i hd
  · exact G.face_subset_complement F hF (G.point_mem_drawing i)
  · exact G.face_subset_complement outer hO (G.point_mem_drawing i)

theorem defect_disjoint (ht : G.TriangleFree) (houter : ¬Bornology.IsBounded outer.val)
    (H : PlaneFace G) (hH : H∈G.defectPlaneFaces ht) (hHF : H≠F) : Disjoint H.val loop.trace := by
  have hHO : H≠outer := by
    intro h
    exact houter (h ▸ G.defectPlaneFace_isBounded ht hH)
  exact ((((G.defectFace_disjoint_trackSpine ht H hH c).union_right
    (G.defectFace_disjoint_trackSpine ht H hH d)).union_right
      (G.faces_disjoint_of_ne H F hHF)).union_right
        (G.faces_disjoint_of_ne H outer hHO)).mono_right hloop

theorem defect_winding_constant (ht : G.TriangleFree) (houter : ¬Bornology.IsBounded outer.val)
    (H : PlaneFace G) (hH : H∈G.defectPlaneFaces ht) (hHF : H≠F) :
    ∀ z∈H.val,loop.windingIndex z=G.faceWindingLabel loop H := by
  intro z hz
  exact loop.windingIndex_constant (G.face_preconnected H) (hloop.defect_disjoint ht houter H hH hHF)
    hz H.property.nonempty.choose_spec

theorem defect_vertex_winding_label (ht : G.TriangleFree) (houter : ¬Bornology.IsBounded outer.val)
    (H : PlaneFace G) (hH : H∈G.defectPlaneFaces ht) (hHF : H≠F) (i : Fin n)
    (hi : G.point i∈closure H.val) : loop.windingIndex (G.point i)=G.faceWindingLabel loop H :=
  loop.windingIndex_eq_of_mem_closure (G.face_preconnected H) (hloop.defect_disjoint ht houter H hH hHF)
    H.property.nonempty.choose_spec hi (hloop.vertex_not_on_loop ht i)

theorem edge_disjoint (ht : G.TriangleFree) (e : OrientedEdge G)
    (hec : edgeComponent e≠c) (hed : edgeComponent e≠d) :
    Disjoint (G.edgeTrace e.val.1 e.val.2) loop.trace := by
  apply Set.disjoint_left.mpr
  intro z hz hzloop
  rcases hloop hzloop with ((hc | hd) | hF) | hO
  · exact Set.disjoint_left.mp (edgeTrace_disjoint_other_spine ht e c hec) hz hc
  · exact Set.disjoint_left.mp (edgeTrace_disjoint_other_spine ht e d hed) hz hd
  · exact G.face_subset_complement F hF (G.edgeTrace_subset_drawing _ _ e.property hz)
  · exact G.face_subset_complement outer hO (G.edgeTrace_subset_drawing _ _ e.property hz)

theorem edge_midpoint_winding_eq (ht : G.TriangleFree) (e : OrientedEdge G)
    (hec : edgeComponent e≠c) (hed : edgeComponent e≠d) :
    loop.windingIndex (G.point e.val.1)=loop.windingIndex (edgeCenter e) := by
  have hpre : IsPreconnected (G.edgeTrace e.val.1 e.val.2) := by
    rw [G.edgeTrace_eq_segment]
    exact (convex_segment (𝕜 := ℝ) _ _).isPreconnected
  apply loop.windingIndex_constant hpre (hloop.edge_disjoint ht e hec hed)
  · exact ⟨0,⟨by norm_num,by norm_num⟩,by simp [PennyGraph.edgePoint]⟩
  · exact ⟨1/2,⟨by norm_num,by norm_num⟩,(edgeCenter_eq_midpoint e).symm⟩

theorem component_disjoint (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht)
    (houter : ¬Bornology.IsBounded outer.val) (v : TrackComponent G)
    (hvc : v≠c) (hvd : v≠d) (hmc : ¬ComponentCrosses v c) (hmd : ¬ComponentCrosses v d) :
    Disjoint (trackSpineTrace v) loop.trace :=
  ((((track_spines_disjoint_of_noncrossing ht hvc hmc).union_right
    (track_spines_disjoint_of_noncrossing ht hvd hmd)).union_right
      (G.defectFace_disjoint_trackSpine ht F hF v).symm).union_right
        (G.track_spine_disjoint_outer ht v outer houter)).mono_right hloop

theorem component_vertex_winding_eq (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht)
    (houter : ¬Bornology.IsBounded outer.val) (e f : OrientedEdge G)
    (hcomp : edgeComponent f=edgeComponent e) (hec : edgeComponent e≠c) (hed : edgeComponent e≠d)
    (hmc : ¬ComponentCrosses (edgeComponent e) c) (hmd : ¬ComponentCrosses (edgeComponent e) d) :
    loop.windingIndex (G.point e.val.1)=loop.windingIndex (G.point f.val.1) := by
  have hE := hloop.edge_midpoint_winding_eq ht e hec hed
  have hF' := hloop.edge_midpoint_winding_eq ht f (hcomp ▸ hec) (hcomp ▸ hed)
  have hcentres := loop.windingIndex_constant (G.trackSpine_preconnected ht (edgeComponent e))
    (hloop.component_disjoint ht hF houter _ hec hed hmc hmd)
    (show edgeCenter e∈trackSpineTrace (edgeComponent e) from Or.inl ⟨e,rfl,rfl⟩)
    (show edgeCenter f∈trackSpineTrace (edgeComponent e) from Or.inl ⟨f,hcomp,rfl⟩)
  exact hE.trans (hcentres.trans hF'.symm)

theorem noncrossing_source_face_labels_eq (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht)
    (houter : ¬Bornology.IsBounded outer.val) (e f : OrientedEdge G)
    (heH : G.sourceFace e∈G.defectPlaneFaces ht) (hfH : G.sourceFace f∈G.defectPlaneFaces ht)
    (heF : G.sourceFace e≠F) (hfF : G.sourceFace f≠F)
    (hcomp : edgeComponent f=edgeComponent e) (hec : edgeComponent e≠c) (hed : edgeComponent e≠d)
    (hmc : ¬ComponentCrosses (edgeComponent e) c) (hmd : ¬ComponentCrosses (edgeComponent e) d) :
    G.faceWindingLabel loop (G.sourceFace e)=G.faceWindingLabel loop (G.sourceFace f) := by
  have h := hloop.component_vertex_winding_eq ht hF houter e f hcomp hec hed hmc hmd
  rw [hloop.defect_vertex_winding_label ht houter _ heH heF _ (G.sourceFace_endpoints_mem_closure e).1,
    hloop.defect_vertex_winding_label ht houter _ hfH hfF _ (G.sourceFace_endpoints_mem_closure f).1] at h
  exact h

end PennyGraph.SpokePairSupport
end Swanepoel
