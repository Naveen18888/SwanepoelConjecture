module
public import Swanepoel.HalfAnchorBound
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

theorem anchor_piece_sum (ht : G.TriangleFree) (hcut : cut∈G.ordinaryTrackComponents)
    (side : Bool) (s t : TrackCutOther cut → OrientedEdge G)
    (hspine : ∀ c, edgeComponent (s c)=c.val ∧ SpineSource (s c) ∧
      (¬∃a,PositiveCellStep (t c) a) ∧ Relation.ReflTransGen PositiveCellStep (s c) (t c)) :
    (∑ c : TrackCutOther cut, (B.bankTerminalPieces ht side (s c) (t c)).card)=
      (B.bankAnchorTracks ht side).card := by
  let A := B.bankAnchorTracks ht side
  have hcutNot : cut∉A := by
    intro hc
    obtain ⟨e,he,heq⟩ := Finset.mem_image.mp hc
    have hp := (Finset.mem_filter.mp he).2
    exact defect_source_component_ne_ordinary ht e hp.1 (Finset.mem_filter.mp hp.2).1 cut hcut heq
  have hcard : ((Finset.univ : Finset (TrackCutOther cut)).filter (fun c => c.val∈A)).card=A.card := by
    apply Finset.card_bij (fun c _ => c.val)
    · intro c hc
      exact (Finset.mem_filter.mp hc).2
    · intro c _ d _ heq
      exact Subtype.ext heq
    · intro c hc
      have hne : c≠cut := fun heq => hcutNot (heq ▸ hc)
      exact ⟨⟨c,hne⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩,rfl⟩
  calc
    _ = ∑ c : TrackCutOther cut, (if c.val∈A then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro c _
      have hs := hspine c
      have hne : edgeComponent (s c)≠cut := fun h => c.property (hs.1.symm.trans h)
      simpa only [hs.1] using B.bankTerminalPieces_card ht side hs.2.1 hs.2.2.1 hs.2.2.2 hne
    _ = ((Finset.univ : Finset (TrackCutOther cut)).filter (fun c => c.val∈A)).card := by
      simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
    _ = _ := hcard

theorem exists_anchor_piece_count (ht : G.TriangleFree) (hcut : cut∈G.ordinaryTrackComponents)
    (side : Bool) : ∃ s t : TrackCutOther cut → OrientedEdge G,
      (∀ c, edgeComponent (s c)=c.val ∧ SpineSource (s c) ∧
        (¬∃a,PositiveCellStep (t c) a) ∧ Relation.ReflTransGen PositiveCellStep (s c) (t c)) ∧
      (∑ c : TrackCutOther cut, (B.bankTerminalPieces ht side (s c) (t c)).card)=
        (B.bankAnchorTracks ht side).card := by
  choose s t hcomp hs htop hst hsep hsame using
    (fun c : TrackCutOther cut => track_cut_spine_endpoint_realization ht c.val cut c.property)
  have hspine : ∀ c, edgeComponent (s c)=c.val ∧ SpineSource (s c) ∧
      (¬∃a,PositiveCellStep (t c) a) ∧ Relation.ReflTransGen PositiveCellStep (s c) (t c) :=
    fun c => ⟨hcomp c,hs c,htop c,hst c⟩
  exact ⟨s,t,hspine,B.anchor_piece_sum ht hcut side s t hspine⟩

end OrdinaryCutBanks
end Swanepoel
