module
public import Swanepoel.CutBankConservation
@[expose] public section
set_option autoImplicit false

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable
namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

theorem missing_crossing_source_bank_eq (ht : G.TriangleFree)
    (e f : OrientedEdge G) (he : SpineSource e) (hf : SpineSource f)
    (heF : G.sourceFace e∈G.defectPlaneFaces ht) (hfF : G.sourceFace f∈G.defectPlaneFaces ht)
    (hne : edgeComponent e≠cut) (hnf : edgeComponent f≠cut)
    (hem : ¬ComponentCrosses (edgeComponent e) cut)
    (hfm : ¬ComponentCrosses (edgeComponent f) cut)
    (hc : ComponentCrosses (edgeComponent e) (edgeComponent f)) :
    B.bankCode (G.sourceFace e)=B.bankCode (G.sourceFace f) := by
  obtain ⟨C,hC⟩ := hc
  have hlabel : B.vertexLabel e.val.1=B.vertexLabel f.val.1 := by
    rcases hC with ⟨ha,hb⟩ | ⟨hb,ha⟩
    · exact (B.noncrossing_carried_vertex_label ht e C.edgeAB he ha hne hem).symm.trans
        (B.noncrossing_carried_vertex_label ht f C.edgeAD hf hb hnf hfm)
    · exact (B.noncrossing_carried_vertex_label ht e C.edgeAD he ha hne hem).symm.trans
        (B.noncrossing_carried_vertex_label ht f C.edgeAB hf hb hnf hfm)
  exact congrArg (fun z : ℤ => decide (z=B.positiveLabel))
    ((B.defect_source_vertex_label ht e heF).symm.trans
      (hlabel.trans (B.defect_source_vertex_label ht f hfF)))

theorem terminal_missing_crossing_same_bank (ht : G.TriangleFree)
    (hcut : cut∈G.ordinaryTrackComponents) (c d : TrackComponent G)
    (hc : c∈G.terminalTrackComponents) (hd : d∈G.terminalTrackComponents)
    (hcd : ComponentCrosses c d) (hcm : c∉B.terminalCutCrossers)
    (hdm : d∉B.terminalCutCrossers) :
    (c∈B.bankAnchorTracks ht false ∧ d∈B.bankAnchorTracks ht false) ∨
      (c∈B.bankAnchorTracks ht true ∧ d∈B.bankAnchorTracks ht true) := by
  rw [← G.familyTrackComponents_all_defects ht] at hc hd
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hd
  have hep := (Finset.mem_filter.mp he).2
  have hfp := (Finset.mem_filter.mp hf).2
  have hne := defect_source_component_ne_ordinary ht e hep.1 hep.2 cut hcut
  have hnf := defect_source_component_ne_ordinary ht f hfp.1 hfp.2 cut hcut
  have hem : ¬ComponentCrosses (edgeComponent e) cut := by
    intro hh
    apply hcm
    refine Finset.mem_filter.mpr ⟨?_,(componentGraph G ht).adj_symm hh⟩
    rw [← G.familyTrackComponents_all_defects ht]
    exact Finset.mem_image.mpr ⟨e,he,rfl⟩
  have hfm : ¬ComponentCrosses (edgeComponent f) cut := by
    intro hh
    apply hdm
    refine Finset.mem_filter.mpr ⟨?_,(componentGraph G ht).adj_symm hh⟩
    rw [← G.familyTrackComponents_all_defects ht]
    exact Finset.mem_image.mpr ⟨f,hf,rfl⟩
  have hl := B.missing_crossing_source_bank_eq ht e f hep.1 hfp.1 hep.2 hfp.2 hne hnf hem hfm hcd
  have hbank (side : Bool) (hs : B.bankCode (G.sourceFace e)=side) :
      edgeComponent e∈B.bankAnchorTracks ht side ∧ edgeComponent f∈B.bankAnchorTracks ht side := by
    exact ⟨Finset.mem_image.mpr ⟨e,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,hep.1,Finset.mem_filter.mpr ⟨hep.2,hs⟩⟩,rfl⟩,
      Finset.mem_image.mpr ⟨f,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,hfp.1,Finset.mem_filter.mpr ⟨hfp.2,hl.symm.trans hs⟩⟩,rfl⟩⟩
  cases hs : B.bankCode (G.sourceFace e)
  · exact Or.inl (hbank false hs)
  · exact Or.inr (hbank true hs)

theorem mem_inheritedNonAnchors (ht : G.TriangleFree) (side : Bool) (c : TrackComponent G) :
    c∈B.inheritedNonAnchors ht side ↔
      c∈G.terminalTrackComponents ∧ ComponentCrosses cut c ∧ c∉B.bankAnchorTracks ht side := by
  simp only [inheritedNonAnchors,terminalCutCrossers,bankMeetingAnchors,
    Finset.mem_sdiff,Finset.mem_filter]
  tauto

def canonicalInheritedNonAnchors (ht : G.TriangleFree) (side : Bool) :
    Finset (B.canonicalHalfTracks ht side).Track :=
  (B.canonicalHalfTracks ht side).ordinary.filter
    (fun u => ComponentCrosses cut (B.canonicalHalfComponent ht side u) ∧
      B.canonicalHalfComponent ht side u∈G.terminalTrackComponents)

theorem canonicalInheritedNonAnchors_image (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool) :
    (B.canonicalInheritedNonAnchors ht side).image (B.canonicalHalfComponent ht side)=
      B.inheritedNonAnchors ht side := by
  let R := B.canonicalHalfBankRealization ht hc hcut side
  have hterm (u : (B.canonicalHalfTracks ht side).Track) :
      u∈(B.canonicalHalfTracks ht side).terminal ↔
        B.canonicalHalfComponent ht side u∈B.bankAnchorTracks ht side := by
    constructor
    · intro hu
      rw [← R.anchors]
      exact Finset.mem_image.mpr ⟨u,hu,rfl⟩
    · intro hu
      rw [← R.anchors] at hu
      obtain ⟨v,hv,hvu⟩ := Finset.mem_image.mp hu
      exact R.injective hvu ▸ hv
  ext c
  constructor
  · intro hc'
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hc'
    have h := Finset.mem_filter.mp hu
    apply (B.mem_inheritedNonAnchors ht side _).mpr
    refine ⟨h.2.2,h.2.1,?_⟩
    intro ha
    exact (Finset.mem_sdiff.mp ((hterm u).mpr ha)).2 h.1
  · intro hc'
    have h := (B.mem_inheritedNonAnchors ht side c).mp hc'
    obtain ⟨a,ha,hac,hcode,_⟩ := B.exists_nonanchor_exterior_source ht side c
      ((componentGraph G ht).adj_symm h.2.1) h.2.2
    have hne : edgeComponent a≠cut := by
      intro heq
      have hcne := (componentGraph G ht).ne_of_adj h.2.1
      exact hcne (heq.symm.trans hac)
    have hva : a.val.1∈B.bankVertices side := (B.mem_bankVertices side _).mpr hcode
    have hvb : a.val.2∈B.bankVertices side := (B.mem_bankVertices side _).mpr
      ((B.noncut_vertexBankCode_eq ht a hne).symm.trans hcode)
    let e := B.liftHalfEdge side a hva hvb
    let u := Fintype.equivFin (TrackComponent (B.halfGraph side)) (edgeComponent e)
    have hmap : B.canonicalHalfComponent ht side u=c := by
      change B.halfComponentMap side
        ((Fintype.equivFin (TrackComponent (B.halfGraph side))).symm
          (Fintype.equivFin (TrackComponent (B.halfGraph side)) (edgeComponent e)))=c
      rw [Equiv.symm_apply_apply,B.halfComponentMap_edge,B.halfEdge_lift]
      exact hac
    have hord : u∈(B.canonicalHalfTracks ht side).ordinary := by
      by_contra hu
      have ht' : u∈(B.canonicalHalfTracks ht side).terminal := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hu⟩
      exact h.2.2 (hmap ▸ (hterm u).mp ht')
    apply Finset.mem_image.mpr
    refine ⟨u,?_,hmap⟩
    have hx : ComponentCrosses cut (B.canonicalHalfComponent ht side u) := by
      rw [hmap]
      exact h.2.1
    have hot : B.canonicalHalfComponent ht side u∈G.terminalTrackComponents := by
      rw [hmap]
      exact h.1
    exact Finset.mem_filter.mpr ⟨hord,hx,hot⟩

theorem canonicalInheritedNonAnchors_card (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool) :
    (B.canonicalInheritedNonAnchors ht side).card=(B.inheritedNonAnchors ht side).card := by
  rw [← B.canonicalInheritedNonAnchors_image ht hc hcut side]
  have hinj : Function.Injective (B.canonicalHalfComponent ht side) :=
    (B.halfComponentMap_injective ht side).comp
      (Fintype.equivFin (TrackComponent (B.halfGraph side))).symm.injective
  exact (Finset.card_image_of_injective _ hinj).symm

end OrdinaryCutBanks
end Swanepoel
