module
public import Swanepoel.L38HalfPentagonComponents
public import Swanepoel.L38HalfAreaFamilyTracks
public import Swanepoel.L38HalfAreaConverse
public import Swanepoel.L38BankCrossingRealization
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

def canonicalHalfTracks (ht : G.TriangleFree) (side : Bool) : TrackSystem :=
  componentSystem (B.halfGraph side) (B.halfGraph_triangleFree ht side)
    (B.halfGraph side).ordinaryTrackComponents ((B.halfGraph side).faceDefectCount (B.halfGraph_triangleFree ht side))

def canonicalHalfComponent (ht : G.TriangleFree) (side : Bool)
    (u : (B.canonicalHalfTracks ht side).Track) : TrackComponent G :=
  B.halfComponentMap side ((Fintype.equivFin (TrackComponent (B.halfGraph side))).symm u)

def canonicalHalfSystem (ht : G.TriangleFree) (side : Bool) : HalfSystem where
  tracks := B.canonicalHalfTracks ht side
  bankAnchors := (B.canonicalHalfTracks ht side).terminal.filter
    (fun u => ComponentCrosses cut (B.canonicalHalfComponent ht side u))
  bank_terminal := Finset.filter_subset _ _
  nonAnchorCrossers := (B.canonicalHalfTracks ht side).ordinary.filter
    (fun u => ComponentCrosses cut (B.canonicalHalfComponent ht side u))
  nonAnchor_ordinary := Finset.filter_subset _ _

theorem canonicalHalf_terminal_iff (ht : G.TriangleFree) (side : Bool)
    (u : (B.canonicalHalfTracks ht side).Track) :
    u∈(B.canonicalHalfTracks ht side).terminal↔
      (Fintype.equivFin (TrackComponent (B.halfGraph side))).symm u∈(B.halfGraph side).terminalTrackComponents := by
  let E := Fintype.equivFin (TrackComponent (B.halfGraph side))
  change u∈Finset.univ\(B.halfGraph side).ordinaryTrackComponents.map E.toEmbedding↔
    E.symm u∈Finset.univ\(B.halfGraph side).ordinaryTrackComponents
  constructor
  · intro hu
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
    intro hm
    exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_map.mpr ⟨E.symm u,hm,E.apply_symm_apply u⟩)
  · intro hu
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
    intro hm
    obtain ⟨c,hc,hcu⟩ := Finset.mem_map.mp hm
    apply (Finset.mem_sdiff.mp hu).2
    rw [← hcu]
    change E.symm (E c)∈(B.halfGraph side).ordinaryTrackComponents
    rw [E.symm_apply_apply]
    exact hc

theorem canonicalHalf_anchors_image (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool) :
    ((B.canonicalHalfTracks ht side).terminal).image (B.canonicalHalfComponent ht side)=B.bankAnchorTracks ht side := by
  let H := B.halfGraph side
  let E := Fintype.equivFin (TrackComponent H)
  have hn : H.terminalTrackComponents.image (B.halfComponentMap side)=B.bankAnchorTracks ht side := by
    rw [← H.familyTrackComponents_all_defects (B.halfGraph_triangleFree ht side),
      ← B.bankDefectImage_all ht hc hcut side,B.bankDefectImage_tracks_image ht side _ _]
    rfl
  rw [← hn]
  ext c
  constructor
  · intro h
    obtain ⟨u,hu,huc⟩ := Finset.mem_image.mp h
    exact Finset.mem_image.mpr ⟨E.symm u,(B.canonicalHalf_terminal_iff ht side u).mp hu,huc⟩
  · intro h
    obtain ⟨d,hd,hdc⟩ := Finset.mem_image.mp h
    refine Finset.mem_image.mpr ⟨E d,(B.canonicalHalf_terminal_iff ht side _).mpr ?_,?_⟩
    · change E.symm (E d)∈H.terminalTrackComponents
      rw [E.symm_apply_apply]
      exact hd
    · change B.halfComponentMap side (E.symm (E d))=c
      rw [E.symm_apply_apply]
      exact hdc

def canonicalHalfBankRealization (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool) :
    (B.canonicalHalfSystem ht side).BankRealization B ht side where
  component := B.canonicalHalfComponent ht side
  injective := (B.halfComponentMap_injective ht side).comp (Fintype.equivFin (TrackComponent (B.halfGraph side))).symm.injective
  anchors := B.canonicalHalf_anchors_image ht hc hcut side
  bank := by
    let A : Finset (Fin (Fintype.card (TrackComponent (B.halfGraph side)))) := (B.canonicalHalfTracks ht side).terminal
    let f : Fin (Fintype.card (TrackComponent (B.halfGraph side)))→TrackComponent G := B.canonicalHalfComponent ht side
    change (A.filter (fun u => ComponentCrosses cut (f u))).image f=_
    calc
      _ = (A.image f).filter (ComponentCrosses cut) := Finset.filter_image.symm
      _ = (B.bankAnchorTracks ht side).filter (ComponentCrosses cut) :=
        congrArg (fun S : Finset (TrackComponent G) => S.filter (ComponentCrosses cut))
          (B.canonicalHalf_anchors_image ht hc hcut side)
      _ = B.bankMeetingAnchors ht side := rfl
  defects := by
    change (B.halfGraph side).faceDefectCount (B.halfGraph_triangleFree ht side)=(B.bankDefectFamily ht side).card
    rw [← (B.halfGraph side).defectPlaneFaces_card (B.halfGraph_triangleFree ht side),
      ← B.bankDefectImage_all ht hc hcut side,B.bankDefectImage_card ht side _ _]
  crosses_cut := fun _ hu => (Finset.mem_filter.mp hu).2
  crossing := by
    intro u _ v _
    exact B.halfComponentMap_crossing_iff ht side _ _
  terminal_crossing := by
    intro u _ v _
    exact B.halfComponentMap_crossing_iff ht side _ _

theorem canonicalHalfBankRealization_terminalCrossing (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool) :
    (B.canonicalHalfBankRealization ht hc hcut side).TerminalCrossing := by
  intro u _ v _
  exact B.halfComponentMap_crossing_iff ht side _ _

theorem canonicalHalf_R_eq_bank (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool) :
    (B.canonicalHalfSystem ht side).R=G.familyR ht (B.bankDefectFamily ht side) :=
  (B.canonicalHalfBankRealization ht hc hcut side).R_eq_actual_bank
    (B.canonicalHalfBankRealization_terminalCrossing ht hc hcut side)

end OrdinaryCutBanks
end Swanepoel
