module
public import Swanepoel.L38HalfAreaRealized
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem PennyGraph.familyOuterSourceEnds_mono {n : ℕ} (G : PennyGraph n)
    {Y Z : Finset (PlaneFace G)} (hYZ : Y⊆Z) :
    G.familyOuterSourceEnds Y⊆G.familyOuterSourceEnds Z := by
  intro e he
  have hep := Finset.mem_filter.mp he
  have hes := (Finset.mem_filter.mp hep.1).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,hes.1,G.familyTrackComponents_mono hYZ hes.2⟩,hep.2⟩

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

def halfBankBoundaryPorts (ht : G.TriangleFree) (side : Bool) : Finset (OrientedEdge (B.halfGraph side)) :=
  ((B.halfGraph side).familyOuterSourceEnds
    ((B.halfGraph side).defectPlaneFaces (B.halfGraph_triangleFree ht side))).filter
      (fun e => ComponentCrosses cut (edgeComponent (B.halfEdge side e)))

def halfBankDart (ht : G.TriangleFree) (side : Bool) (e : OrientedEdge (B.halfGraph side)) : Prop :=
  e∈B.halfBankBoundaryPorts ht side

def halfWeightedLength (ht : G.TriangleFree) (side : Bool) (e : OrientedEdge (B.halfGraph side)) : ℝ :=
  (B.halfGraph side).l38TrackWeight (B.halfRemainderDefects ht side)
    (B.halfIsolatedDefects ht side) (edgeComponent e)

def halfBankAxis (side : Bool) : Plane := -B.signedVector side

theorem halfBankAxis_norm (side : Bool) : ‖B.halfBankAxis side‖=1 := by
  rw [halfBankAxis,norm_neg,B.signedVector_norm side]

theorem halfWeightedLength_nonneg (ht : G.TriangleFree) (side : Bool)
    (e : OrientedEdge (B.halfGraph side)) : 0≤B.halfWeightedLength ht side e :=
  (B.halfGraph side).l38TrackWeight_nonneg _ _ _

theorem half_defect_source_old_bank (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool)
    (e : OrientedEdge (B.halfGraph side))
    (he : (B.halfGraph side).sourceFace e∈
      (B.halfGraph side).defectPlaneFaces (B.halfGraph_triangleFree ht side)) :
    SpineSource (B.halfEdge side e) ∧
      G.sourceFace (B.halfEdge side e)∈B.bankDefectFamily ht side := by
  obtain ⟨F,hF,hFace⟩ := B.half_defect_bank_face_surjective ht hc hcut side _ he
  have hOld := (B.bankDefect_sourceFace_iff ht side F hF e).mp hFace.symm
  have hOldDef : G.sourceFace (B.halfEdge side e)∈G.defectPlaneFaces ht :=
    hOld ▸ (Finset.mem_filter.mp hF).1
  exact ⟨G.spineSource_of_sourceFace_mem_defects ht _ hOldDef,hOld ▸ hF⟩

theorem halfBankDart_normal_cone (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool)
    (f : OrientedEdge (B.halfGraph side)) (hf : B.halfBankDart ht side f) :
    Real.sqrt 3/2 < inner ℝ (B.halfBankAxis side) (sourceNormal f) := by
  have hfp := Finset.mem_filter.mp hf
  have hfOuter := Finset.mem_filter.mp hfp.1
  have hfs := (Finset.mem_filter.mp hfOuter.1).2
  obtain ⟨e,he,hef⟩ := Finset.mem_image.mp hfs.2
  have hep := (Finset.mem_filter.mp he).2
  have heOld := B.half_defect_source_old_bank ht hc hcut side e hep.2
  have hcompOld : edgeComponent (B.halfEdge side e)=edgeComponent (B.halfEdge side f) :=
    congrArg (B.halfComponentMap side) hef
  have heCross : ComponentCrosses (edgeComponent (B.halfEdge side e)) cut := by
    rw [hcompOld]
    exact (componentGraph G ht).adj_symm hfp.2
  have hsharp := B.crossing_signed_normal_cone ht (B.halfEdge side e) heOld.1
    (Finset.mem_filter.mp heOld.2).1 heCross
  rw [(Finset.mem_filter.mp heOld.2).2] at hsharp
  have hne : f≠e := by
    intro h
    subst f
    exact hfOuter.2 ((B.halfGraph side).defectPlaneFace_isBounded (B.halfGraph_triangleFree ht side) hep.2)
  have hn := source_normals_opposite (B.halfGraph_triangleFree ht side) hep.1 hfs.1 hef.symm hne
  have hnormal : sourceNormal (B.halfEdge side e)=sourceNormal e := by
    unfold sourceNormal
    rw [B.halfEdge_vector]
  rw [hn,halfBankAxis,inner_neg_left,inner_neg_right,neg_neg]
  rwa [hnormal] at hsharp

theorem halfBankBoundaryPorts_subset_outer (ht : G.TriangleFree) (side : Bool)
    (outer : PlaneFace (B.halfGraph side)) (houter : ¬Bornology.IsBounded outer.val) :
    B.halfBankBoundaryPorts ht side⊆(B.halfGraph side).faceIncidentDarts outer := by
  intro e he
  have heOuter := Finset.mem_filter.mp (Finset.mem_filter.mp he).1
  obtain ⟨O,hO,hunique⟩ := (B.halfGraph side).exists_unique_outer_face
  have hFace : (B.halfGraph side).sourceFace e=outer :=
    (hunique _ heOuter.2).trans (hunique _ houter).symm
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hFace⟩

def crossingOuterBankFamily (ht : G.TriangleFree) (side : Bool)
    (Y : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side) :
    Finset (OrientedEdge (B.halfGraph side)) :=
  ((B.halfGraph side).familyOuterSourceEnds (B.bankDefectImage ht side Y hY)).filter
    (fun e => ComponentCrosses cut (edgeComponent (B.halfEdge side e)))

theorem subfamilyMeetingTracks_eq_filter (ht : G.TriangleFree) (side : Bool)
    (Y : Finset (PlaneFace G)) (_hY : Y⊆B.bankDefectFamily ht side) :
    B.subfamilyMeetingTracks Y=(G.familyTrackComponents Y).filter (ComponentCrosses cut) := by
  ext c
  constructor
  · intro hc
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hc
    have hep := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨e,hep.1,rfl⟩,hep.2⟩
  · intro hc
    have hcp := Finset.mem_filter.mp hc
    obtain ⟨e,he,hec⟩ := Finset.mem_image.mp hcp.1
    exact Finset.mem_image.mpr ⟨e,Finset.mem_filter.mpr ⟨he,by rw [hec]; exact hcp.2⟩,hec⟩

theorem crossingOuterBankFamily_image (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool)
    (Y : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side) :
    (B.crossingOuterBankFamily ht side Y hY).image (fun e => edgeComponent (B.halfEdge side e))=
      (G.familyTrackComponents Y).filter (ComponentCrosses cut) := by
  ext c
  constructor
  · intro hcMem
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hcMem
    have hfp := Finset.mem_filter.mp hf
    have hfs := (Finset.mem_filter.mp (Finset.mem_filter.mp hfp.1).1).2
    have hOldTrack : edgeComponent (B.halfEdge side f)∈G.familyTrackComponents Y := by
      rw [← B.bankDefectImage_tracks_image ht side Y hY]
      exact Finset.mem_image.mpr ⟨edgeComponent f,hfs.2,rfl⟩
    exact Finset.mem_filter.mpr ⟨hOldTrack,hfp.2⟩
  · intro hcMem
    have hcp := Finset.mem_filter.mp hcMem
    obtain ⟨g,hg,hgc⟩ := Finset.mem_image.mp hcp.1
    have hgp := (Finset.mem_filter.mp hg).2
    have hgBankMeet : g∈B.subfamilyMeetingPorts (B.bankDefectFamily ht side) :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hgp.1,hY hgp.2⟩,
        by rw [hgc]; exact hcp.2⟩
    have hgFree := B.subfamilyMeetingPorts_subset_unpaired ht side (B.bankDefectFamily ht side)
      (Finset.Subset.refl _) hgBankMeet
    have hgImage : g∈((B.halfGraph side).familySourcePorts (B.bankDefectImage ht side Y hY)).image (B.halfEdge side) := by
      rw [B.bankDefectImage_sourcePorts_image ht side Y hY]
      exact hg
    obtain ⟨gH,hgH,hgEq⟩ := Finset.mem_image.mp hgImage
    have hgHP := (Finset.mem_filter.mp hgH).2
    have hgDef := B.bankDefectImage_subset_defects ht side Y hY hgHP.2
    have hgHalfFree : B.halfEdge side gH∈G.familyUnpairedPorts (B.bankDefectFamily ht side) := by
      rw [hgEq]
      exact hgFree
    have hb := B.half_unpaired_component_boundary ht side (B.half_defect_bank_face_surjective ht hc hcut side)
      gH hgHP.1 hgDef hgHalfFree
    obtain ⟨f,hf,hfc⟩ := Finset.mem_image.mp hb
    have hfo := Finset.mem_filter.mp hf
    have hfs := (Finset.mem_filter.mp hfo.1).2
    have hfY : f∈(B.halfGraph side).familyOuterSourceEnds (B.bankDefectImage ht side Y hY) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hfs.1,?_⟩,hfo.2⟩
      rw [hfc]
      exact Finset.mem_image.mpr ⟨gH,hgH,rfl⟩
    have hfcOld : edgeComponent (B.halfEdge side f)=c := by
      have hh := congrArg (B.halfComponentMap side) hfc
      change edgeComponent (B.halfEdge side f)=edgeComponent (B.halfEdge side gH) at hh
      rw [hgEq] at hh
      exact hh.trans hgc
    exact Finset.mem_image.mpr ⟨f,Finset.mem_filter.mpr ⟨hfY,by rw [hfcOld]; exact hcp.2⟩,hfcOld⟩

theorem crossingOuterBankFamily_card (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool)
    (Y : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side)
    (hclosed : (B.halfGraph side).IsJoinClosed (B.halfGraph_triangleFree ht side)
      (B.bankDefectImage ht side Y hY)) :
    (B.crossingOuterBankFamily ht side Y hY).card=(B.subfamilyMeetingPorts Y).card := by
  have houterSub := (B.halfGraph side).familyOuterSourceEnds_subset_terminal
    (B.halfGraph_triangleFree ht side) hclosed
  have hinj : Set.InjOn (fun e => edgeComponent (B.halfEdge side e))
      (B.crossingOuterBankFamily ht side Y hY : Set (OrientedEdge (B.halfGraph side))) := by
    intro e he f hf hOld
    have hep := Finset.mem_filter.mp he
    have hfp := Finset.mem_filter.mp hf
    have hes := (Finset.mem_filter.mp (Finset.mem_filter.mp hep.1).1).2
    have hfs := (Finset.mem_filter.mp (Finset.mem_filter.mp hfp.1).1).2
    have hcomp := B.bankDefectImage_tracks_map_injOn ht side Y hY hes.2 hfs.2 hOld
    exact (B.halfGraph side).terminalOuterSourceEnds_component_injOn (B.halfGraph_triangleFree ht side)
      (houterSub hep.1) (houterSub hfp.1) hcomp
  rw [← Finset.card_image_of_injOn hinj,B.crossingOuterBankFamily_image ht hc hcut side Y hY,
    ← B.subfamilyMeetingTracks_eq_filter ht side Y hY,B.subfamilyMeetingTracks_card ht side Y hY]

theorem halfBankBoundaryPorts_filter_family (ht : G.TriangleFree) (side : Bool)
    (Y : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side) :
    (B.halfBankBoundaryPorts ht side).filter
      (fun e => edgeComponent e∈(B.halfGraph side).familyTrackComponents (B.bankDefectImage ht side Y hY))=
        B.crossingOuterBankFamily ht side Y hY := by
  ext e
  constructor
  · intro he
    have hep := Finset.mem_filter.mp he
    have heb := Finset.mem_filter.mp hep.1
    have heo := Finset.mem_filter.mp heb.1
    have hes := (Finset.mem_filter.mp heo.1).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hes.1,hep.2⟩,heo.2⟩,heb.2⟩
  · intro he
    have hep := Finset.mem_filter.mp he
    have heo := Finset.mem_filter.mp hep.1
    have hes := (Finset.mem_filter.mp heo.1).2
    have hAll := (B.halfGraph side).familyOuterSourceEnds_mono
      (B.bankDefectImage_subset_defects ht side Y hY) hep.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hAll,hep.2⟩,hes.2⟩

theorem halfBankBoundary_weighted_mass (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool) :
    (∑ e∈B.halfBankBoundaryPorts ht side,B.halfWeightedLength ht side e)=
      (B.isolatedTwoPortPentagons ht side).card+(B.subfamilyMeetingPorts (B.bankRemainder ht side)).card := by
  have hSSub : B.isolatedTwoPortPentagons ht side⊆B.bankDefectFamily ht side := Finset.filter_subset _ _
  have hCount (Y : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side)
      (hclosed : (B.halfGraph side).IsJoinClosed (B.halfGraph_triangleFree ht side)
        (B.bankDefectImage ht side Y hY)) :
      (∑ e∈B.halfBankBoundaryPorts ht side,
        if edgeComponent e∈(B.halfGraph side).familyTrackComponents (B.bankDefectImage ht side Y hY)
          then (1:ℝ) else 0)=(B.subfamilyMeetingPorts Y).card := by
    rw [← Finset.sum_filter,B.halfBankBoundaryPorts_filter_family ht side Y hY]
    simpa using congrArg (fun k : ℕ => (k:ℝ)) (B.crossingOuterBankFamily_card ht hc hcut side Y hY hclosed)
  have hY := hCount (B.bankRemainder ht side) (B.bankRemainder_subset ht side)
    (B.halfRemainderDefects_joinClosed ht hc hcut side)
  have hS := hCount (B.isolatedTwoPortPentagons ht side) hSSub
    (B.halfIsolatedDefects_joinClosed ht hc hcut side)
  have hSpecial : (B.subfamilyMeetingPorts (B.isolatedTwoPortPentagons ht side)).card=
      2*(B.isolatedTwoPortPentagons ht side).card := by
    rw [B.subfamilyMeetingPorts_card_eq_sum]
    calc
      _ = ∑ _∈B.isolatedTwoPortPentagons ht side,2 :=
        Finset.sum_congr rfl (fun F hF => (Finset.mem_filter.mp hF).2.2.1)
      _ = _ := by simp [Nat.mul_comm]
  have hSreal : ((B.subfamilyMeetingPorts (B.isolatedTwoPortPentagons ht side)).card : ℝ)=
      2*(B.isolatedTwoPortPentagons ht side).card := by exact_mod_cast hSpecial
  have hHalf : (∑ e∈B.halfBankBoundaryPorts ht side,
      if edgeComponent e∈(B.halfGraph side).familyTrackComponents (B.halfIsolatedDefects ht side)
        then (1/2:ℝ) else 0)=
      (1/2:ℝ)*(∑ e∈B.halfBankBoundaryPorts ht side,
        if edgeComponent e∈(B.halfGraph side).familyTrackComponents (B.halfIsolatedDefects ht side)
          then (1:ℝ) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> norm_num
  change (∑ e∈B.halfBankBoundaryPorts ht side,
    ((if edgeComponent e∈(B.halfGraph side).familyTrackComponents (B.halfRemainderDefects ht side)
      then (1:ℝ) else 0)+
    (if edgeComponent e∈(B.halfGraph side).familyTrackComponents (B.halfIsolatedDefects ht side)
      then (1/2:ℝ) else 0)))=_
  rw [Finset.sum_add_distrib,hHalf]
  change (∑ e∈B.halfBankBoundaryPorts ht side,
      if edgeComponent e∈(B.halfGraph side).familyTrackComponents
        (B.bankDefectImage ht side (B.bankRemainder ht side) (B.bankRemainder_subset ht side)) then (1:ℝ) else 0)+
      (1/2:ℝ)*(∑ e∈B.halfBankBoundaryPorts ht side,
      if edgeComponent e∈(B.halfGraph side).familyTrackComponents
        (B.bankDefectImage ht side (B.isolatedTwoPortPentagons ht side) hSSub) then (1:ℝ) else 0)=_
  rw [hY,hS,hSreal]
  ring

theorem halfBankDart_sum (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool)
    (outer : PlaneFace (B.halfGraph side)) (houter : ¬Bornology.IsBounded outer.val) :
    (∑ e∈(B.halfGraph side).faceIncidentDarts outer,
      if B.halfBankDart ht side e then B.halfWeightedLength ht side e else 0)=
      (B.isolatedTwoPortPentagons ht side).card+(B.subfamilyMeetingPorts (B.bankRemainder ht side)).card := by
  have hSub := B.halfBankBoundaryPorts_subset_outer ht side outer houter
  have hfilter : ((B.halfGraph side).faceIncidentDarts outer).filter
      (fun e => B.halfBankDart ht side e)=B.halfBankBoundaryPorts ht side := by
    ext e
    constructor
    · intro he
      exact (Finset.mem_filter.mp he).2
    · intro he
      exact Finset.mem_filter.mpr ⟨hSub he,he⟩
  rw [← Finset.sum_filter,hfilter]
  exact B.halfBankBoundary_weighted_mass ht hc hcut side

end OrdinaryCutBanks
end Swanepoel
