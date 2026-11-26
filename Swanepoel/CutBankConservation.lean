module
public import Swanepoel.L38Lemma
@[expose] public section
set_option autoImplicit false

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable
namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

def terminalCutCrossers (_B : OrdinaryCutBanks G cut) : Finset (TrackComponent G) :=
  G.terminalTrackComponents.filter (ComponentCrosses cut)

def splitTerminalJoins (ht : G.TriangleFree) : Finset (TrackComponent G) :=
  B.bankAnchorTracks ht false ∩ B.bankAnchorTracks ht true

def inheritedNonAnchors (ht : G.TriangleFree) (side : Bool) : Finset (TrackComponent G) :=
  B.terminalCutCrossers \ B.bankMeetingAnchors ht side

theorem bankDefectFamily_partition (ht : G.TriangleFree) :
    Disjoint (B.bankDefectFamily ht false) (B.bankDefectFamily ht true) ∧
    B.bankDefectFamily ht false ∪ B.bankDefectFamily ht true=G.defectPlaneFaces ht := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro F hF hT
    have h := (Finset.mem_filter.mp hF).2.symm.trans (Finset.mem_filter.mp hT).2
    cases h
  · ext F
    cases h : B.bankCode F <;> simp [bankDefectFamily,h]

theorem bank_defect_count_conservation (ht : G.TriangleFree) :
    (B.bankDefectFamily ht false).card+(B.bankDefectFamily ht true).card=G.faceDefectCount ht := by
  rw [← Finset.card_union_of_disjoint (B.bankDefectFamily_partition ht).1,
    (B.bankDefectFamily_partition ht).2,G.defectPlaneFaces_card ht]

theorem bankAnchorTracks_union (ht : G.TriangleFree) :
    B.bankAnchorTracks ht false ∪ B.bankAnchorTracks ht true=G.terminalTrackComponents := by
  unfold bankAnchorTracks
  rw [← G.familyTrackComponents_union,(B.bankDefectFamily_partition ht).2,
    G.familyTrackComponents_all_defects ht]

theorem splitTerminalJoins_cross (ht : G.TriangleFree)
    (hcut : cut∈G.ordinaryTrackComponents) {c : TrackComponent G}
    (hc : c∈B.splitTerminalJoins ht) : ComponentCrosses cut c := by
  obtain ⟨he,hf⟩ := Finset.mem_inter.mp hc
  obtain ⟨e,he,hec⟩ := Finset.mem_image.mp he
  obtain ⟨f,hf,hfc⟩ := Finset.mem_image.mp hf
  have hp := (Finset.mem_filter.mp he).2
  have hq := (Finset.mem_filter.mp hf).2
  have hne : edgeComponent e≠cut :=
    defect_source_component_ne_ordinary ht e hp.1 (Finset.mem_filter.mp hp.2).1 cut hcut
  by_contra hx
  have hmiss : ¬ComponentCrosses (edgeComponent e) cut := by
    intro hh
    exact hx (hec ▸ (componentGraph G ht).adj_symm hh)
  have hl := B.missing_source_face_labels_eq ht e f hp.1 hq.1
    (Finset.mem_filter.mp hp.2).1 (Finset.mem_filter.mp hq.2).1
    (hfc.trans hec.symm) hne hmiss
  have hcode : B.bankCode (G.sourceFace e)=B.bankCode (G.sourceFace f) :=
    congrArg (fun z : ℤ => decide (z=B.positiveLabel)) hl
  rw [(Finset.mem_filter.mp hp.2).2,(Finset.mem_filter.mp hq.2).2] at hcode
  cases hcode

theorem bankMeetingAnchors_union (ht : G.TriangleFree) :
    B.bankMeetingAnchors ht false ∪ B.bankMeetingAnchors ht true=B.terminalCutCrossers := by
  unfold bankMeetingAnchors terminalCutCrossers
  rw [← Finset.filter_union,B.bankAnchorTracks_union ht]

theorem bankMeetingAnchors_inter (ht : G.TriangleFree)
    (hcut : cut∈G.ordinaryTrackComponents) :
    B.bankMeetingAnchors ht false ∩ B.bankMeetingAnchors ht true=B.splitTerminalJoins ht := by
  ext c
  constructor
  · intro hc
    exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_inter.mp hc).1).1,
      (Finset.mem_filter.mp (Finset.mem_inter.mp hc).2).1⟩
  · intro hc
    have hx := B.splitTerminalJoins_cross ht hcut hc
    exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hc).1,hx⟩,
      Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hc).2,hx⟩⟩

theorem bank_anchor_count_conservation (ht : G.TriangleFree) :
    (B.bankAnchorTracks ht false).card+(B.bankAnchorTracks ht true).card=
      G.terminalTrackComponents.card+(B.splitTerminalJoins ht).card := by
  have h := Finset.card_union_add_card_inter (B.bankAnchorTracks ht false) (B.bankAnchorTracks ht true)
  rw [B.bankAnchorTracks_union ht] at h
  exact h.symm

theorem bank_K_conservation (ht : G.TriangleFree) :
    B.bankK ht false+B.bankK ht true=
      (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).K+
        (B.splitTerminalJoins ht).card := by
  have hp := B.bank_anchor_count_conservation ht
  have hf := B.bank_defect_count_conservation ht
  rw [G.componentSystem_K_eq]
  unfold bankK
  omega

theorem bank_meeting_count_conservation (ht : G.TriangleFree)
    (hcut : cut∈G.ordinaryTrackComponents) :
    (B.bankMeetingAnchors ht false).card+(B.bankMeetingAnchors ht true).card=
      B.terminalCutCrossers.card+(B.splitTerminalJoins ht).card := by
  have h := Finset.card_union_add_card_inter (B.bankMeetingAnchors ht false) (B.bankMeetingAnchors ht true)
  rw [B.bankMeetingAnchors_union ht,B.bankMeetingAnchors_inter ht hcut] at h
  exact h.symm

theorem bank_meeting_subset_crossers (ht : G.TriangleFree) (side : Bool) :
    B.bankMeetingAnchors ht side⊆B.terminalCutCrossers := by
  cases side
  · exact (Finset.subset_union_left.trans_eq (B.bankMeetingAnchors_union ht))
  · exact (Finset.subset_union_right.trans_eq (B.bankMeetingAnchors_union ht))

theorem bank_meeting_nonanchor_count (ht : G.TriangleFree) (side : Bool) :
    (B.bankMeetingAnchors ht side).card+(B.inheritedNonAnchors ht side).card=
      B.terminalCutCrossers.card := by
  have h := Finset.card_sdiff_add_card_eq_card (B.bank_meeting_subset_crossers ht side)
  unfold inheritedNonAnchors
  omega

theorem split_join_count_le_meeting (ht : G.TriangleFree)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool) :
    (B.splitTerminalJoins ht).card≤(B.bankMeetingAnchors ht side).card := by
  apply Finset.card_le_card
  rw [← B.bankMeetingAnchors_inter ht hcut]
  cases side
  · exact Finset.inter_subset_left
  · exact Finset.inter_subset_right

end OrdinaryCutBanks
end Swanepoel
