module
public import Swanepoel.JoinClosedFamilies
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def PennyGraph.familyBoundaryDefectPorts {n : ℕ} (G : PennyGraph n)
    (Y : Finset (PlaneFace G)) : Finset (OrientedEdge G) :=
  (G.familySourcePorts Y).filter (fun e => edgeComponent e∈G.familyBoundaryTrackComponents Y)

def PennyGraph.familyBoundaryPortCount {n : ℕ} (G : PennyGraph n)
    (Y : Finset (PlaneFace G)) (F : PlaneFace G) : ℕ :=
  ((G.faceSourcePorts F).filter (fun e => edgeComponent e∈G.familyBoundaryTrackComponents Y)).card

theorem PennyGraph.familyBoundaryPortCount_le {n : ℕ} (G : PennyGraph n)
    (Y : Finset (PlaneFace G)) (F : PlaneFace G) :
    G.familyBoundaryPortCount Y F≤(G.faceSourcePorts F).card :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem PennyGraph.bounded_sources_eq_on_boundary_track {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    {e f : OrientedEdge G} (he : e∈G.familySourcePorts Y) (hf : f∈G.familySourcePorts Y)
    (hc : edgeComponent e=edgeComponent f)
    (hb : edgeComponent e∈G.familyBoundaryTrackComponents Y) : e=f := by
  obtain ⟨g,hg,hgc⟩ := Finset.mem_image.mp hb
  have hgeSource := (Finset.mem_filter.mp (Finset.mem_filter.mp hg).1).2.1
  have hgOuter := (Finset.mem_filter.mp hg).2
  have hep := (Finset.mem_filter.mp he).2
  have hfp := (Finset.mem_filter.mp hf).2
  have heBound := G.defectPlaneFace_isBounded ht (hY.subset_defects hep.2)
  have hfBound := G.defectPlaneFace_isBounded ht (hY.subset_defects hfp.2)
  have hge : g≠e := by intro hh; subst g; exact hgOuter heBound
  have hgf : g≠f := by intro hh; subst g; exact hgOuter hfBound
  obtain ⟨s,t,_,hall⟩ := component_sources ht (edgeComponent e)
  have hePair := (hall e).mp ⟨hep.1,rfl⟩
  have hfPair := (hall f).mp ⟨hfp.1,hc.symm⟩
  have hgPair := (hall g).mp ⟨hgeSource,hgc⟩
  rcases hePair with hs | ht
  · rcases hfPair with hfs | hft
    · exact hs.trans hfs.symm
    · rcases hgPair with hgs | hgt
      · exact False.elim (hge (hgs.trans hs.symm))
      · exact False.elim (hgf (hgt.trans hft.symm))
  · rcases hfPair with hfs | hft
    · rcases hgPair with hgs | hgt
      · exact False.elim (hgf (hgs.trans hfs.symm))
      · exact False.elim (hge (hgt.trans ht.symm))
    · exact ht.trans hft.symm

theorem PennyGraph.familyBoundaryDefectPorts_component_injOn {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) :
    Set.InjOn edgeComponent (G.familyBoundaryDefectPorts Y : Set (OrientedEdge G)) := by
  intro e he f hf hc
  exact G.bounded_sources_eq_on_boundary_track ht hY
    (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp hf).1 hc (Finset.mem_filter.mp he).2

theorem PennyGraph.familyBoundaryDefectPorts_image {n : ℕ} (G : PennyGraph n)
    (Y : Finset (PlaneFace G)) :
    (G.familyBoundaryDefectPorts Y).image edgeComponent=G.familyBoundaryTrackComponents Y := by
  ext c
  constructor
  · rintro hc
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hc
    exact (Finset.mem_filter.mp he).2
  · intro hc
    obtain ⟨g,hg,hgc⟩ := Finset.mem_image.mp hc
    have hgTrack := (Finset.mem_filter.mp (Finset.mem_filter.mp hg).1).2.2
    obtain ⟨e,he,hec⟩ := Finset.mem_image.mp hgTrack
    have hec' : edgeComponent e=c := hec.trans hgc
    exact Finset.mem_image.mpr ⟨e,Finset.mem_filter.mpr ⟨he,hec' ▸ hc⟩,hec'⟩

theorem PennyGraph.familyBoundaryDefectPorts_count {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) :
    (G.familyBoundaryDefectPorts Y).card=G.familyBoundaryEndCount Y := by
  rw [← Finset.card_image_of_injOn (G.familyBoundaryDefectPorts_component_injOn ht hY),
    G.familyBoundaryDefectPorts_image,G.familyBoundaryTrackComponents_count ht hY]

theorem PennyGraph.sum_familyBoundaryPortCount {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) :
    (∑ F ∈ Y, G.familyBoundaryPortCount Y F)=G.familyBoundaryEndCount Y := by
  have hcard := Finset.card_eq_sum_card_fiberwise
    (f := G.sourceFace) (s := G.familyBoundaryDefectPorts Y) (t := Y)
    (fun e he => (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2.2)
  rw [← G.familyBoundaryDefectPorts_count ht hY,hcard]
  apply Finset.sum_congr rfl
  intro F hF
  change ((G.faceSourcePorts F).filter
    (fun e => edgeComponent e∈G.familyBoundaryTrackComponents Y)).card=_
  congr 1
  ext e
  simp only [PennyGraph.faceSourcePorts,PennyGraph.familyBoundaryDefectPorts,
    PennyGraph.familySourcePorts,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨hs,hface⟩,hb⟩
    exact ⟨⟨⟨hs,hface ▸ hF⟩,hb⟩,hface⟩
  · rintro ⟨⟨⟨hs,_⟩,hb⟩,hface⟩
    exact ⟨⟨hs,hface⟩,hb⟩

end Swanepoel
