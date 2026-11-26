module
public import Swanepoel.HalfSectorPorts
@[expose] public section

noncomputable section
namespace Swanepoel
open Set
attribute [local instance] Classical.propDecidable

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

def cutPieceVertexLabel (ht : G.TriangleFree) : TrackCutComponent cut → ℤ :=
  Quotient.lift (fun e : OrientedEdge G => B.vertexLabel e.val.1) (by
    intro e f h
    induction h with
    | rel e f h => exact h.start_vertex_winding_eq ht cut B.outer B.loop B.support
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

def cutPieceBankCode (ht : G.TriangleFree) (p : TrackCutComponent cut) : Bool :=
  decide (B.cutPieceVertexLabel ht p=B.positiveLabel)

theorem cutPieceBankCode_source (ht : G.TriangleFree) (e : OrientedEdge G)
    (hF : G.sourceFace e∈G.defectPlaneFaces ht) :
    B.cutPieceBankCode ht (trackCutComponent cut e)=B.bankCode (G.sourceFace e) := by
  unfold cutPieceBankCode bankCode
  change decide (B.vertexLabel e.val.1=B.positiveLabel)=_
  rw [B.defect_source_vertex_label ht e hF]

theorem cutPieceBankCode_reverse (ht : G.TriangleFree) (e : OrientedEdge G)
    (hne : edgeComponent e≠cut) :
    B.cutPieceBankCode ht (trackCutComponent cut (reverseEdge e))=
      B.cutPieceBankCode ht (trackCutComponent cut e) := by
  have hh := G.noncut_edge_winding_equal ht cut B.outer B.loop B.support e hne
  unfold cutPieceBankCode
  change decide (B.vertexLabel e.val.2=B.positiveLabel)=decide (B.vertexLabel e.val.1=B.positiveLabel)
  exact congrArg (fun z : ℤ => decide (z=B.positiveLabel)) hh.symm

theorem bankMeetingAnchors_miss (ht : G.TriangleFree) (side : Bool)
    (v : TrackComponent G) (hcross : ComponentCrosses cut v)
    (c : TrackComponent G) (hc : c∈B.bankMeetingAnchors ht side) :
    ¬ComponentCrosses v c := by
  intro hvc
  have hcu := (Finset.mem_filter.mp hc).2
  exact componentGraph_noTriple G ht cut v c hcross hvc ((componentGraph G ht).adj_symm hcu)

theorem crossing_bank_sources_eq (ht : G.TriangleFree) (side : Bool)
    (e f : OrientedEdge G) (he : SpineSource e) (hf : SpineSource f)
    (heY : G.sourceFace e∈B.bankDefectFamily ht side)
    (hfY : G.sourceFace f∈B.bankDefectFamily ht side)
    (hc : edgeComponent f=edgeComponent e)
    (hcross : ComponentCrosses (edgeComponent e) cut) : e=f := by
  by_contra hne
  have hcode : B.bankCode (G.sourceFace e)=B.bankCode (G.sourceFace f) :=
    (Finset.mem_filter.mp heY).2.trans (Finset.mem_filter.mp hfY).2.symm
  have hp := B.crossing_signed_normal_pos ht e he (Finset.mem_filter.mp heY).1 hcross
  have hq := B.crossing_signed_normal_pos ht f hf (Finset.mem_filter.mp hfY).1 (hc ▸ hcross)
  have hn := source_normals_opposite ht he hf hc (Ne.symm hne)
  rw [hn,inner_neg_right,← hcode] at hq
  linarith

theorem crossing_old_ends_not_both_in_half (ht : G.TriangleFree) (side : Bool)
    {s t : OrientedEdge G} (hs : SpineSource s) (htop : ¬∃g,PositiveCellStep t g)
    (hst : Relation.ReflTransGen PositiveCellStep s t)
    (hcross : ComponentCrosses (edgeComponent s) cut) :
    ¬(G.sourceFace s∈B.bankDefectFamily ht side ∧
      G.sourceFace (reverseEdge t)∈B.bankDefectFamily ht side) := by
  rintro ⟨hS,hT⟩
  have hrt : SpineSource (reverseEdge t) := by
    rintro ⟨g,hg⟩
    have hh := hg.reverse
    simp only [reverseEdge_involutive] at hh
    exact htop ⟨reverseEdge g,hh⟩
  have hcomp : edgeComponent (reverseEdge t)=edgeComponent s :=
    (reverse_component t).symm.trans (positive_path_component hst).symm
  have heq := B.crossing_bank_sources_eq ht side s (reverseEdge t) hs hrt hS hT hcomp hcross
  exact spine_opposite_sources_ne hst heq

def bankTerminalPieces (ht : G.TriangleFree) (side : Bool) (s t : OrientedEdge G) :
    Finset (TrackCutComponent cut) :=
  (if G.sourceFace s∈B.bankDefectFamily ht side then {trackCutComponent cut s} else ∅) ∪
  (if G.sourceFace (reverseEdge t)∈B.bankDefectFamily ht side then {trackCutComponent cut t} else ∅)

theorem anchor_iff_old_source_in_half (ht : G.TriangleFree) (side : Bool)
    {s t : OrientedEdge G} (hs : SpineSource s) (htop : ¬∃g,PositiveCellStep t g)
    (hst : Relation.ReflTransGen PositiveCellStep s t) :
    edgeComponent s∈B.bankAnchorTracks ht side ↔
      G.sourceFace s∈B.bankDefectFamily ht side ∨
      G.sourceFace (reverseEdge t)∈B.bankDefectFamily ht side := by
  have hrt : SpineSource (reverseEdge t) := by
    rintro ⟨g,hg⟩
    have hh := hg.reverse
    simp only [reverseEdge_involutive] at hh
    exact htop ⟨reverseEdge g,hh⟩
  have hcomp : edgeComponent (reverseEdge t)=edgeComponent s :=
    (reverse_component t).symm.trans (positive_path_component hst).symm
  constructor
  · intro hc
    obtain ⟨e,he,hec⟩ := Finset.mem_image.mp hc
    have hep := (Finset.mem_filter.mp he).2
    have hm : e∈originalTrackSources (edgeComponent s) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hep.1,hec⟩
    rw [complete_spine_original_sources ht hs htop hst] at hm
    rcases Finset.mem_insert.mp hm with h | h
    · exact Or.inl (h ▸ hep.2)
    · exact Or.inr ((Finset.mem_singleton.mp h) ▸ hep.2)
  · intro h
    rcases h with h | h
    · exact Finset.mem_image.mpr ⟨s,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs,h⟩,rfl⟩
    · exact Finset.mem_image.mpr ⟨reverseEdge t,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,hrt,h⟩,hcomp⟩

theorem bankTerminalPieces_card (ht : G.TriangleFree) (side : Bool)
    {s t : OrientedEdge G} (hs : SpineSource s) (htop : ¬∃g,PositiveCellStep t g)
    (hst : Relation.ReflTransGen PositiveCellStep s t) (hne : edgeComponent s≠cut) :
    (B.bankTerminalPieces ht side s t).card=
      if edgeComponent s∈B.bankAnchorTracks ht side then 1 else 0 := by
  have hanchor := B.anchor_iff_old_source_in_half ht side hs htop hst
  by_cases hc : ComponentCrosses (edgeComponent s) cut
  · have hnot := B.crossing_old_ends_not_both_in_half ht side hs htop hst hc
    by_cases hS : G.sourceFace s∈B.bankDefectFamily ht side
    · have hT : G.sourceFace (reverseEdge t)∉B.bankDefectFamily ht side := fun hT => hnot ⟨hS,hT⟩
      simp [bankTerminalPieces,hanchor,hS,hT]
    · by_cases hT : G.sourceFace (reverseEdge t)∈B.bankDefectFamily ht side <;>
        simp [bankTerminalPieces,hanchor,hS,hT]
  · have heq : trackCutComponent cut s=trackCutComponent cut t := by
      apply Quotient.sound
      exact Relation.EqvGen.reflTransGen_le_eqvGen _ _ _ (noncrossing_path_preserved ht hne hc hst)
    by_cases hS : G.sourceFace s∈B.bankDefectFamily ht side <;>
      by_cases hT : G.sourceFace (reverseEdge t)∈B.bankDefectFamily ht side <;>
      simp [bankTerminalPieces,heq,hanchor,hS,hT]

theorem nonanchor_source_unbounded (ht : G.TriangleFree) (side : Bool)
    (e : OrientedEdge G) (he : SpineSource e)
    (hside : B.cutPieceBankCode ht (trackCutComponent cut e)=side)
    (hnot : edgeComponent e∉B.bankAnchorTracks ht side) :
    ¬Bornology.IsBounded (G.sourceFace e).val := by
  rcases G.sourceFace_defect_or_unbounded ht e he with hF | hF
  · have hcode := B.cutPieceBankCode_source ht e hF
    have heY : G.sourceFace e∈B.bankDefectFamily ht side :=
      Finset.mem_filter.mpr ⟨hF,hcode.symm.trans hside⟩
    exact False.elim (hnot (Finset.mem_image.mpr
      ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he,heY⟩,rfl⟩))
  · exact hF

end OrdinaryCutBanks
end Swanepoel
