module
public import Swanepoel.SpineBankSeparation
public import Swanepoel.TrackCutSources
@[expose] public section

noncomputable section
namespace Swanepoel
open Set
attribute [local instance] Classical.propDecidable

theorem PositiveCellStep.start_vertex_winding_of_side_ne_cut {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) (cut : TrackComponent G) (outer : PlaneFace G)
    {a : Plane} (loop : PlaneChain a a) (hloop : loop.trace⊆trackSpineTrace cut∪outer.val)
    {e f : OrientedEdge G} (C : RhombusCell G)
    (hE : e.val=(C.a,C.b)) (hF : f.val=(C.d,C.c))
    (hside : edgeComponent C.edgeAD≠cut) :
    loop.windingIndex (G.point e.val.1)=loop.windingIndex (G.point f.val.1) := by
  simpa only [hE,hF,RhombusCell.edgeAD] using G.noncut_edge_winding_equal ht cut outer loop hloop C.edgeAD hside

theorem TrackCutStep.start_vertex_winding_eq {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) (cut : TrackComponent G) (outer : PlaneFace G)
    {a : Plane} (loop : PlaneChain a a) (hloop : loop.trace⊆trackSpineTrace cut∪outer.val)
    {e f : OrientedEdge G} (hstep : TrackCutStep cut e f) :
    loop.windingIndex (G.point e.val.1)=loop.windingIndex (G.point f.val.1) := by
  obtain ⟨q,hq,hnot⟩ := hstep
  obtain ⟨C,hE,hF,_⟩ := q.property
  have heq : q.val.1=C.edgeAB := Subtype.ext hE
  have hfq : q.val.2=C.edgeDC := Subtype.ext hF
  have hcorners : q.rhombus.representative.corners=C.corners := by
    rw [q.rhombus.representative_corners]
    change stepCorners q.val.1 q.val.2=C.corners
    rw [heq,hfq,C.stepCorners_eq]
  have hside : edgeComponent C.edgeAD≠cut := by
    intro hs
    apply hnot
    have hp := q.rhombus.representative.trackPair_of_corners ht C hcorners
    change s(edgeComponent q.rhombus.representative.edgeAB,
        edgeComponent q.rhombus.representative.edgeAD)=s(edgeComponent C.edgeAB,edgeComponent C.edgeAD) at hp
    rcases Sym2.eq_iff.mp hp with h | h
    · exact Or.inr (h.2.trans hs)
    · exact Or.inl (h.1.trans hs)
  have h := PositiveCellStep.start_vertex_winding_of_side_ne_cut ht cut outer loop hloop C hE hF hside
  simpa only [hq] using h

theorem trackCut_path_start_vertex_winding_eq {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) (cut : TrackComponent G) (outer : PlaneFace G)
    {a : Plane} (loop : PlaneChain a a) (hloop : loop.trace⊆trackSpineTrace cut∪outer.val)
    {e f : OrientedEdge G} (hpath : Relation.ReflTransGen (TrackCutStep cut) e f) :
    loop.windingIndex (G.point e.val.1)=loop.windingIndex (G.point f.val.1) := by
  induction hpath with
  | refl => rfl
  | tail _ h ih => exact ih.trans (h.start_vertex_winding_eq ht cut outer loop hloop)

theorem PennyGraph.noncrossing_source_vertex_winding_eq {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (cut : TrackComponent G) (outer : PlaneFace G)
    {a : Plane} (loop : PlaneChain a a) (hloop : loop.trace⊆trackSpineTrace cut∪outer.val)
    (e f : OrientedEdge G) (he : SpineSource e) (hf : SpineSource f)
    (hcomp : edgeComponent f=edgeComponent e) (hne : edgeComponent e≠cut)
    (hmiss : ¬ComponentCrosses (edgeComponent e) cut) :
    loop.windingIndex (G.point e.val.1)=loop.windingIndex (G.point f.val.1) := by
  obtain ⟨s,t,hs,htop,hE,_⟩ := component_spine_iff ht e
  have hse : s=e := source_path_eq he hE.1
  subst s
  have hst := hE.1.trans hE.2
  have hmem : f∈originalTrackSources (edgeComponent e) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf,hcomp⟩
  rw [complete_spine_original_sources ht hs htop hst] at hmem
  rcases Finset.mem_insert.mp hmem with hfe | hft
  · rw [hfe]
  · have hft' : f=reverseEdge t := Finset.mem_singleton.mp hft
    have hpath := noncrossing_path_preserved ht hne hmiss hst
    have hstart := trackCut_path_start_vertex_winding_eq ht cut outer loop hloop hpath
    have htc : edgeComponent t=edgeComponent e := (positive_path_component hst).symm
    have hlast := G.noncut_edge_winding_equal ht cut outer loop hloop t (htc ▸ hne)
    exact hstart.trans (by simpa only [hft',reverseEdge] using hlast)

theorem PennyGraph.noncrossing_defect_source_labels_eq {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (cut : TrackComponent G) (outer : PlaneFace G)
    (houter : ¬Bornology.IsBounded outer.val) {a : Plane} (loop : PlaneChain a a)
    (hloop : loop.trace⊆trackSpineTrace cut∪outer.val)
    (e f : OrientedEdge G) (he : SpineSource e) (hf : SpineSource f)
    (heF : G.sourceFace e∈G.defectPlaneFaces ht) (hfF : G.sourceFace f∈G.defectPlaneFaces ht)
    (hcomp : edgeComponent f=edgeComponent e) (hne : edgeComponent e≠cut)
    (hmiss : ¬ComponentCrosses (edgeComponent e) cut) :
    G.faceWindingLabel loop (G.sourceFace e)=G.faceWindingLabel loop (G.sourceFace f) := by
  have hv := G.noncrossing_source_vertex_winding_eq ht cut outer loop hloop e f he hf hcomp hne hmiss
  rw [G.defect_vertex_winding_label ht cut outer houter loop hloop _ heF _
    (G.sourceFace_endpoints_mem_closure e).1,
    G.defect_vertex_winding_label ht cut outer houter loop hloop _ hfF _
    (G.sourceFace_endpoints_mem_closure f).1] at hv
  exact hv

end Swanepoel
