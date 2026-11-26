module
public import Swanepoel.TwoSpineTransport
@[expose] public section

noncomputable section
namespace Swanepoel
open Set
attribute [local instance] Classical.propDecidable

theorem two_spine_masked_path_winding_eq {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) (u v : TrackComponent G) (outer : PlaneFace G)
    {a : Plane} (loop : PlaneChain a a)
    (hloop : loop.trace⊆(trackSpineTrace u∪trackSpineTrace v)∪outer.val)
    {e f : OrientedEdge G} (hpath : Relation.ReflTransGen (TrackCutStep v) e f)
    (hne : edgeComponent e≠u) (hmiss : ¬ComponentCrosses (edgeComponent e) u) :
    loop.windingIndex (G.point e.val.1)=loop.windingIndex (G.point f.val.1) := by
  induction hpath with
  | refl => rfl
  | @tail x y hx hxy ih =>
    have hpos := Relation.ReflTransGen.mono (fun _ _ h => h.to_positive) _ _ hx
    have hc := (positive_path_component hpos).symm
    have hu := noncrossing_step_preserved ht (hc ▸ hne) (hc ▸ hmiss) hxy.to_positive
    obtain ⟨C,hX,hY,_⟩ := hxy.to_positive
    have hh := G.noncut_edge_two_spine_winding_equal ht u v outer loop hloop C.edgeAD
      (hu.other_component_ne ht C hX hY) (hxy.other_component_ne ht C hX hY)
    exact ih.trans (by simpa only [hX,hY,RhombusCell.edgeAD] using hh)

theorem PennyGraph.noncrossing_two_spine_source_labels_eq {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (u v : TrackComponent G) (outer : PlaneFace G)
    (houter : ¬Bornology.IsBounded outer.val) {a : Plane} (loop : PlaneChain a a)
    (hloop : loop.trace⊆(trackSpineTrace u∪trackSpineTrace v)∪outer.val)
    (e f : OrientedEdge G) (he : SpineSource e) (hf : SpineSource f)
    (heF : G.sourceFace e∈G.defectPlaneFaces ht) (hfF : G.sourceFace f∈G.defectPlaneFaces ht)
    (hcomp : edgeComponent f=edgeComponent e) (hnu : edgeComponent e≠u) (hnv : edgeComponent e≠v)
    (hmu : ¬ComponentCrosses (edgeComponent e) u) (hmv : ¬ComponentCrosses (edgeComponent e) v) :
    G.faceWindingLabel loop (G.sourceFace e)=G.faceWindingLabel loop (G.sourceFace f) := by
  have hvertex : loop.windingIndex (G.point e.val.1)=loop.windingIndex (G.point f.val.1) := by
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
      have hpath := noncrossing_path_preserved ht hnv hmv hst
      have hstart := two_spine_masked_path_winding_eq ht u v outer loop hloop hpath hnu hmu
      have htc : edgeComponent t=edgeComponent e := (positive_path_component hst).symm
      have hlast := G.noncut_edge_two_spine_winding_equal ht u v outer loop hloop t (htc ▸ hnu) (htc ▸ hnv)
      exact hstart.trans (by simpa only [hft',reverseEdge] using hlast)
  rw [G.defect_vertex_two_spine_label ht u v outer houter loop hloop _ heF _
      (G.sourceFace_endpoints_mem_closure e).1,
    G.defect_vertex_two_spine_label ht u v outer houter loop hloop _ hfF _
      (G.sourceFace_endpoints_mem_closure f).1] at hvertex
  exact hvertex

end Swanepoel
