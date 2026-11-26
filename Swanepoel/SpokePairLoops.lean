module
public import Swanepoel.PentagonSpokes
public import Swanepoel.HalfLocalCutLoop
@[expose] public section

noncomputable section
namespace Swanepoel
open Set
attribute [local instance] Classical.propDecidable

namespace PlaneChain
def changeEndpoints {a b c d : Plane} (p : PlaneChain a b) (ha : a=c) (hb : b=d) : PlaneChain c d := by
  cases ha
  cases hb
  exact p

theorem trace_changeEndpoints {a b c d : Plane} (p : PlaneChain a b) (ha : a=c) (hb : b=d) :
    (p.changeEndpoints ha hb).trace=p.trace := by
  cases ha
  cases hb
  rfl
end PlaneChain

theorem PennyGraph.face_midpoint_chain {n : ℕ} (G : PennyGraph n)
    (F : PlaneFace G) (e f : OrientedEdge G)
    (he : G.sourceFace e=F) (hf : G.sourceFace f=F) :
    ∃ arc : PlaneChain (edgeCenter e) (edgeCenter f),
      arc.trace⊆({edgeCenter e,edgeCenter f} : Set Plane)∪F.val := by
  have hep : G.sourceProbe e∈F.val := by rw [← he]; exact G.sourceProbe_mem_sourceFace e
  have hfp : G.sourceProbe f∈F.val := by rw [← hf]; exact G.sourceProbe_mem_sourceFace f
  obtain ⟨inside,hinside⟩ := planeChain_of_segment_reachable hep (G.face_segment_reachable F hep hfp)
  let first := PlaneChain.single (edgeCenter e) (G.sourceProbe e)
  let last := PlaneChain.single (G.sourceProbe f) (edgeCenter f)
  let arc := (first.append inside).append last
  have hcE := G.source_probe_connector_subset e
  have hcF := G.source_probe_connector_subset f
  rw [he] at hcE
  rw [hf] at hcF
  refine ⟨arc,?_⟩
  simp only [arc,first,last,PlaneChain.trace_append,PlaneChain.trace_single]
  refine Set.union_subset (Set.union_subset ?_ (hinside.trans Set.subset_union_right)) ?_
  · exact hcE.trans (Set.union_subset
      (by intro z hz; exact Or.inl (Or.inl (Set.mem_singleton_iff.mp hz))) Set.subset_union_right)
  · rw [segment_symm]
    exact hcF.trans (Set.union_subset
      (by intro z hz; exact Or.inl (Or.inr hz)) Set.subset_union_right)

theorem PennyGraph.boundary_port_complete_spine_to_outer {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    (F : PlaneFace G) (hFY : F∈Y)
    (hports : ∀ e∈G.faceSourcePorts F,edgeComponent e∈G.familyBoundaryTrackComponents Y)
    (outer : PlaneFace G) (houter : ¬Bornology.IsBounded outer.val)
    (e : OrientedEdge G) (he : e∈G.faceSourcePorts F) :
    ∃ t : OrientedEdge G, (¬∃g,PositiveCellStep t g) ∧
      Relation.ReflTransGen PositiveCellStep e t ∧ G.sourceFace (reverseEdge t)=outer := by
  have heSource := (Finset.mem_filter.mp he).2.1
  obtain ⟨s,t,hs,htop,hE,_⟩ := component_spine_iff ht e
  have hse : s=e := source_path_eq heSource hE.1
  subst s
  have hreach := hE.1.trans hE.2
  have hrt : SpineSource (reverseEdge t) := by
    rintro ⟨g,hg⟩
    have hh := hg.reverse
    simp only [reverseEdge_involutive] at hh
    exact htop ⟨reverseEdge g,hh⟩
  have hc : edgeComponent e=edgeComponent (reverseEdge t) :=
    (positive_path_component hreach).trans (reverse_component t)
  have hne : reverseEdge t≠e := (spine_opposite_sources_ne hreach).symm
  have hrtOuter := G.boundary_face_other_source_end_unbounded ht hY F hFY hports he hrt hc hne
  obtain ⟨O,_,hunique⟩ := G.exists_unique_outer_face
  exact ⟨t,htop,hreach,(hunique _ hrtOuter).trans (hunique _ houter).symm⟩

theorem PennyGraph.boundary_spoke_pair_loop {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    (F : PlaneFace G) (hFY : F∈Y)
    (hports : ∀ e∈G.faceSourcePorts F,edgeComponent e∈G.familyBoundaryTrackComponents Y)
    (outer : PlaneFace G) (houter : ¬Bornology.IsBounded outer.val)
    (e f : OrientedEdge G) (he : e∈G.faceSourcePorts F) (hf : f∈G.faceSourcePorts F) :
    ∃ loop : PlaneChain (edgeCenter e) (edgeCenter e),
      trackSpineTrace (edgeComponent e)⊆loop.trace ∧
      trackSpineTrace (edgeComponent f)⊆loop.trace ∧
      loop.trace⊆((trackSpineTrace (edgeComponent e)∪trackSpineTrace (edgeComponent f))∪F.val)∪outer.val := by
  obtain ⟨t,htop,het,htF⟩ := G.boundary_port_complete_spine_to_outer ht hY F hFY hports outer houter e he
  obtain ⟨u,huTop,hfu,huF⟩ := G.boundary_port_complete_spine_to_outer ht hY F hFY hports outer houter f hf
  obtain ⟨p⟩ := PositiveSpineChain.exists_of_reach het
  obtain ⟨q⟩ := PositiveSpineChain.exists_of_reach hfu
  have heSource := (Finset.mem_filter.mp he).2.1
  have hfSource := (Finset.mem_filter.mp hf).2.1
  have hp : p.toPlane.trace=trackSpineTrace (edgeComponent e) := p.complete_trace ht heSource htop
  have hq : q.toPlane.trace=trackSpineTrace (edgeComponent f) := q.complete_trace ht hfSource huTop
  obtain ⟨inside,hinside⟩ := G.face_midpoint_chain F f e
    (Finset.mem_filter.mp hf).2.2 (Finset.mem_filter.mp he).2.2
  obtain ⟨outsideRaw,houtsideRaw⟩ := G.face_midpoint_chain outer (reverseEdge t) (reverseEdge u) htF huF
  let outside := outsideRaw.changeEndpoints (edgeCenter_reverse t) (edgeCenter_reverse u)
  have houtside : outside.trace⊆({edgeCenter t,edgeCenter u} : Set Plane)∪outer.val := by
    rw [PlaneChain.trace_changeEndpoints]
    simpa only [edgeCenter_reverse] using houtsideRaw
  let loop := ((p.toPlane.append outside).append q.toPlane.reverse).append inside
  have hsE : edgeCenter e∈trackSpineTrace (edgeComponent e) := Or.inl ⟨e,rfl,rfl⟩
  have hsF : edgeCenter f∈trackSpineTrace (edgeComponent f) := Or.inl ⟨f,rfl,rfl⟩
  have htE : edgeCenter t∈trackSpineTrace (edgeComponent e) :=
    Or.inl ⟨t,(positive_path_component het).symm,rfl⟩
  have huF' : edgeCenter u∈trackSpineTrace (edgeComponent f) :=
    Or.inl ⟨u,(positive_path_component hfu).symm,rfl⟩
  refine ⟨loop,?_,?_,?_⟩
  · rw [← hp]
    simp only [loop,PlaneChain.trace_append]
    exact Set.subset_union_left.trans (Set.subset_union_left.trans Set.subset_union_left)
  · rw [← hq,← PlaneChain.trace_reverse q.toPlane]
    simp only [loop,PlaneChain.trace_append]
    exact Set.subset_union_right.trans Set.subset_union_left
  · simp only [loop,PlaneChain.trace_append,PlaneChain.trace_reverse,hp,hq]
    refine Set.union_subset (Set.union_subset (Set.union_subset ?_ ?_) ?_) ?_
    · exact fun _ hz => Or.inl (Or.inl (Or.inl hz))
    · intro z hz
      rcases houtside hz with hz | hz
      · rcases hz with hzt | hzu
        · exact Or.inl (Or.inl (Or.inl (hzt.symm ▸ htE)))
        · exact Or.inl (Or.inl (Or.inr ((Set.mem_singleton_iff.mp hzu).symm ▸ huF')))
      · exact Or.inr hz
    · exact fun _ hz => Or.inl (Or.inl (Or.inr hz))
    · intro z hz
      rcases hinside hz with hz | hz
      · rcases hz with hzf | hze
        · exact Or.inl (Or.inl (Or.inr (hzf.symm ▸ hsF)))
        · exact Or.inl (Or.inl (Or.inl ((Set.mem_singleton_iff.mp hze).symm ▸ hsE)))
      · exact Or.inl (Or.inr hz)

end Swanepoel
