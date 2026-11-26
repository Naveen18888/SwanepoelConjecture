module
public import Swanepoel.SpokePairBanks
@[expose] public section

noncomputable section
namespace Swanepoel
open Set
attribute [local instance] Classical.propDecidable

abbrev PennyGraph.SpokeClosingSupport {n : ℕ} (G : PennyGraph n) (cut : TrackComponent G)
    (F outer : PlaneFace G) (e t : OrientedEdge G) (close : PlaneChain (edgeCenter t) (edgeCenter e)) : Prop :=
  close.trace⊆((trackSpineTrace cut∪({edgeCenter e,edgeCenter t} : Set Plane))∪F.val)∪outer.val

theorem PennyGraph.boundary_spoke_closing_route {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    (F : PlaneFace G) (hFY : F∈Y)
    (hports : ∀ s∈G.faceSourcePorts F,edgeComponent s∈G.familyBoundaryTrackComponents Y)
    (outer : PlaneFace G) (houter : ¬Bornology.IsBounded outer.val)
    (e f : OrientedEdge G) (he : e∈G.faceSourcePorts F) (hf : f∈G.faceSourcePorts F)
    (t : OrientedEdge G) (htF : G.sourceFace (reverseEdge t)=outer) :
    ∃ close : PlaneChain (edgeCenter t) (edgeCenter e),
      G.SpokeClosingSupport (edgeComponent f) F outer e t close ∧
      trackSpineTrace (edgeComponent f)⊆close.trace := by
  obtain ⟨u,huTop,hfu,huF⟩ := G.boundary_port_complete_spine_to_outer ht hY F hFY hports outer houter f hf
  obtain ⟨q⟩ := PositiveSpineChain.exists_of_reach hfu
  have hq := q.complete_trace ht (Finset.mem_filter.mp hf).2.1 huTop
  obtain ⟨inside,hinside⟩ := G.face_midpoint_chain F f e
    (Finset.mem_filter.mp hf).2.2 (Finset.mem_filter.mp he).2.2
  obtain ⟨outsideRaw,houtsideRaw⟩ := G.face_midpoint_chain outer (reverseEdge t) (reverseEdge u) htF huF
  let outside := outsideRaw.changeEndpoints (edgeCenter_reverse t) (edgeCenter_reverse u)
  have houtside : outside.trace⊆({edgeCenter t,edgeCenter u} : Set Plane)∪outer.val := by
    rw [PlaneChain.trace_changeEndpoints]
    simpa only [edgeCenter_reverse] using houtsideRaw
  let close := (outside.append q.toPlane.reverse).append inside
  have hsF : edgeCenter f∈trackSpineTrace (edgeComponent f) := Or.inl ⟨f,rfl,rfl⟩
  have huF' : edgeCenter u∈trackSpineTrace (edgeComponent f) :=
    Or.inl ⟨u,(positive_path_component hfu).symm,rfl⟩
  refine ⟨close,?_,?_⟩
  · dsimp only [PennyGraph.SpokeClosingSupport]
    simp only [close,PlaneChain.trace_append,PlaneChain.trace_reverse,hq]
    refine Set.union_subset (Set.union_subset ?_ ?_) ?_
    · intro z hz
      rcases houtside hz with hz | hz
      · rcases hz with hzt | hzu
        · exact Or.inl (Or.inl (Or.inr (Or.inr hzt)))
        · exact Or.inl (Or.inl (Or.inl ((Set.mem_singleton_iff.mp hzu).symm ▸ huF')))
      · exact Or.inr hz
    · exact fun _ hz => Or.inl (Or.inl (Or.inl hz))
    · intro z hz
      rcases hinside hz with hz | hz
      · rcases hz with hzf | hze
        · exact Or.inl (Or.inl (Or.inl (hzf.symm ▸ hsF)))
        · exact Or.inl (Or.inl (Or.inr (Or.inl (Set.mem_singleton_iff.mp hze))))
      · exact Or.inl (Or.inr hz)
  · rw [← hq,← PlaneChain.trace_reverse q.toPlane]
    simp only [close,PlaneChain.trace_append]
    exact Set.subset_union_right.trans Set.subset_union_left

theorem PositiveCellStep.midpoint_not_spoke_closing {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {a b e t : OrientedEdge G} (hab : PositiveCellStep a b)
    (hc : edgeComponent a=edgeComponent e) (cut : TrackComponent G)
    (hne : edgeComponent e≠cut) (hmiss : ¬ComponentCrosses (edgeComponent e) cut)
    (F outer : PlaneFace G) (hF : F∈G.defectPlaneFaces ht) (houter : ¬Bornology.IsBounded outer.val)
    (close : PlaneChain (edgeCenter t) (edgeCenter e))
    (hclose : G.SpokeClosingSupport cut F outer e t close) : stepCenter a b∉close.trace := by
  obtain ⟨C,hA,hB,_⟩ := hab
  have ha : a=C.edgeAB := Subtype.ext hA
  have hb : b=C.edgeDC := Subtype.ext hB
  have hcenter : stepCenter a b=C.center := by rw [ha,hb,C.stepCenter_eq]
  have hAB : edgeComponent C.edgeAB=edgeComponent e := ha ▸ hc
  have hAD : edgeComponent C.edgeAD≠cut := by
    intro h
    exact hmiss ⟨C,Or.inl ⟨hAB,h⟩⟩
  have hmem : stepCenter a b∈C.closedRegion := by
    rw [hcenter,← C.cellPoint_half_eq_center]
    exact C.openRegion_subset_closedRegion (C.cellPoint_mem_openRegion ht
      (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have hnotDrawing : stepCenter a b∉G.drawing := by
    rw [hcenter,← C.cellPoint_half_eq_center]
    exact C.openRegion_subset_complement ht (C.cellPoint_mem_openRegion ht
      (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  intro hz
  rcases hclose hz with ((hcut | hend) | hface) | hout
  · exact Set.disjoint_left.mp (C.closedRegion_disjoint_other_spine ht cut
      (hAB ▸ hne) hAD) hmem hcut
  · rcases hend with hs | ht'
    · exact hnotDrawing (hs.symm ▸ G.edgeCenter_mem_drawing e)
    · exact hnotDrawing ((Set.mem_singleton_iff.mp ht').symm ▸ G.edgeCenter_mem_drawing t)
  · exact Set.disjoint_left.mp (G.defectFace_disjoint_closedRhombus ht F hF C) hface hmem
  · exact Set.disjoint_left.mp (G.closedRhombus_disjoint_unbounded_face ht C outer houter) hmem hout

end Swanepoel
