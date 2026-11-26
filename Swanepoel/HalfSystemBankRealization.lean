module
public import Swanepoel.BankAnchorPieceCounts
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

structure HalfSystem.BankRealization {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G}
    (H : HalfSystem) (B : OrdinaryCutBanks G cut) (ht : G.TriangleFree) (side : Bool) where
  component : H.tracks.Track → TrackComponent G
  injective : Function.Injective component
  anchors : H.tracks.terminal.image component=B.bankAnchorTracks ht side
  bank : H.bankAnchors.image component=B.bankMeetingAnchors ht side
  defects : H.tracks.defects=(B.bankDefectFamily ht side).card
  crosses_cut : ∀ u∈H.nonAnchorCrossers, ComponentCrosses cut (component u)
  crossing : ∀ u∈H.nonAnchorCrossers, ∀ t∈H.tracks.terminal,
    H.tracks.crossing.Adj u t ↔ ComponentCrosses (component u) (component t)
  terminal_crossing : ∀ u∈H.tracks.terminal, ∀ v∈H.tracks.terminal,
    H.tracks.crossing.Adj u v ↔ ComponentCrosses (component u) (component v)

theorem HalfSystem.BankRealization.nonAnchorBound {n : ℕ} {G : PennyGraph n}
    {cut : TrackComponent G} {H : HalfSystem} {B : OrdinaryCutBanks G cut}
    {ht : G.TriangleFree} {side : Bool} (R : H.BankRealization B ht side)
    (hdegree : ∀ a b, G.graph.Adj a b → ∃ c, G.graph.Adj a c ∧ c≠b)
    (hcut : cut∈G.ordinaryTrackComponents) : H.NonAnchorBound := by
  have hp : H.tracks.p=(B.bankAnchorTracks ht side).card := by
    rw [← R.anchors,Finset.card_image_of_injective _ R.injective]
    rfl
  have hd : H.bankAnchors.card=(B.bankMeetingAnchors ht side).card := by
    rw [← R.bank,Finset.card_image_of_injective _ R.injective]
  intro u hu
  have hnot : R.component u∉B.bankAnchorTracks ht side := by
    rw [← R.anchors]
    intro hmem
    obtain ⟨t,ht,hcomp⟩ := Finset.mem_image.mp hmem
    have htu := R.injective hcomp
    subst t
    exact (Finset.mem_sdiff.mp ht).2 (H.nonAnchor_ordinary hu)
  have himage : (H.tracks.terminal.filter (H.tracks.crossing.Adj u)).image R.component=
      (B.bankAnchorTracks ht side).filter (ComponentCrosses (R.component u)) := by
    ext c
    constructor
    · rintro hc
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hc
      have ht' := Finset.mem_filter.mp ht
      exact Finset.mem_filter.mpr ⟨R.anchors ▸ Finset.mem_image.mpr ⟨t,ht'.1,rfl⟩,
        (R.crossing u hu t ht'.1).mp ht'.2⟩
    · intro hc
      have hc' := Finset.mem_filter.mp hc
      rw [← R.anchors] at hc'
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hc'.1
      exact Finset.mem_image.mpr ⟨t,Finset.mem_filter.mpr ⟨ht,(R.crossing u hu t ht).mpr hc'.2⟩,rfl⟩
  have hs : H.tracks.s u=((B.bankAnchorTracks ht side).filter (ComponentCrosses (R.component u))).card := by
    rw [← himage,Finset.card_image_of_injective _ R.injective]
    rfl
  have hbound := B.nonAnchor_bound ht hdegree hcut side (R.component u) (R.crosses_cut u hu) hnot
  change (H.tracks.s u : ℤ)≤H.tracks.K-(H.bankAnchors.card : ℤ)
  rw [hs,hd,TrackSystem.K,hp,R.defects]
  exact hbound

end Swanepoel
