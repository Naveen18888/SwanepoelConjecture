module
public import Swanepoel.L38HalfPentagonCrossings
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

theorem half_component_old_source (ht : G.TriangleFree) (side : Bool)
    (e : OrientedEdge (B.halfGraph side)) :
    ∃ s : OrientedEdge (B.halfGraph side),SpineSource (B.halfEdge side s) ∧ edgeComponent s=edgeComponent e := by
  have hne := B.halfEdge_ne_cut ht side e
  have liftSource (a : OrientedEdge G) (hs : SpineSource a)
      (hc : edgeComponent a=edgeComponent (B.halfEdge side e))
      (hcode : B.cutPieceBankCode ht (trackCutComponent cut a)=side) :
      ∃ s : OrientedEdge (B.halfGraph side),SpineSource (B.halfEdge side s) ∧ edgeComponent s=edgeComponent e := by
    have ha : a.val.1∈B.bankVertices side := (B.mem_bankVertices side _).mpr hcode
    have hna : edgeComponent a≠cut := by rw [hc]; exact hne
    have hb : a.val.2∈B.bankVertices side := (B.mem_bankVertices side _).mpr
      ((B.noncut_vertexBankCode_eq ht a hna).symm.trans hcode)
    let s := B.liftHalfEdge side a ha hb
    have hmap : B.halfEdge side s=a := B.halfEdge_lift side a ha hb
    have hs' : SpineSource (B.halfEdge side s) := by rw [hmap]; exact hs
    refine ⟨s,hs',B.half_component_eq_of_old_source ht side s e hs' ?_⟩
    rw [hmap]
    exact hc.symm
  by_cases hx : ComponentCrosses (edgeComponent (B.halfEdge side e)) cut
  · by_cases hanchor : edgeComponent (B.halfEdge side e)∈B.bankAnchorTracks ht side
    · obtain ⟨a,ha,hc⟩ := Finset.mem_image.mp hanchor
      have hp := (Finset.mem_filter.mp ha).2
      apply liftSource a hp.1 hc
      exact (B.cutPieceBankCode_source ht a (Finset.mem_filter.mp hp.2).1).trans (Finset.mem_filter.mp hp.2).2
    · obtain ⟨a,hs,hc,hcode,_⟩ := B.exists_nonanchor_exterior_source ht side
        (edgeComponent (B.halfEdge side e)) hx hanchor
      exact liftSource a hs hc hcode
  · obtain ⟨s,t,hs,_,hE,_⟩ := component_spine_iff ht (B.halfEdge side e)
    have hsc : edgeComponent s=edgeComponent (B.halfEdge side e) := positive_path_component hE.1
    have hns : edgeComponent s≠cut := by rw [hsc]; exact hne
    have hms : ¬ComponentCrosses (edgeComponent s) cut := by rw [hsc]; exact hx
    have hl := B.noncrossing_carried_vertex_label ht s (B.halfEdge side e) hs hsc.symm hns hms
    apply liftSource s hs hsc
    change decide (B.vertexLabel s.val.1=B.positiveLabel)=side
    rw [← hl]
    exact (B.mem_bankVertices side _).mp (B.halfVertex_mem side e.val.1)

theorem halfComponentMap_injective (ht : G.TriangleFree) (side : Bool) :
    Function.Injective (B.halfComponentMap side) := by
  intro c d h
  obtain ⟨s,hs,hsc⟩ := B.half_component_old_source ht side c.out
  obtain ⟨t,_,htd⟩ := B.half_component_old_source ht side d.out
  have hsc' : edgeComponent s=c := hsc.trans (Quotient.out_eq c)
  have htd' : edgeComponent t=d := htd.trans (Quotient.out_eq d)
  have hold : edgeComponent (B.halfEdge side s)=edgeComponent (B.halfEdge side t) := by
    rw [← B.halfComponentMap_edge,← B.halfComponentMap_edge,hsc',htd']
    exact h
  exact hsc'.symm.trans ((B.half_component_eq_of_old_source ht side s t hs hold.symm).trans htd')

theorem halfComponentMap_crossing_iff (ht : G.TriangleFree) (side : Bool)
    (c d : TrackComponent (B.halfGraph side)) :
    ComponentCrosses c d↔ComponentCrosses (B.halfComponentMap side c) (B.halfComponentMap side d) := by
  obtain ⟨s,hs,hsc⟩ := B.half_component_old_source ht side c.out
  obtain ⟨t,hts,htd⟩ := B.half_component_old_source ht side d.out
  have hsc' : edgeComponent s=c := hsc.trans (Quotient.out_eq c)
  have htd' : edgeComponent t=d := htd.trans (Quotient.out_eq d)
  rw [← hsc',← htd',B.halfComponentMap_edge,B.halfComponentMap_edge]
  exact B.half_old_source_crossing_iff ht side s t hs hts

theorem halfComponentMap_ne_cut (ht : G.TriangleFree) (side : Bool)
    (c : TrackComponent (B.halfGraph side)) : B.halfComponentMap side c≠cut := by
  refine Quotient.inductionOn c ?_
  intro e
  exact B.halfEdge_ne_cut ht side e

end OrdinaryCutBanks
end Swanepoel
