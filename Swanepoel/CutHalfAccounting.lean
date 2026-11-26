module
public import Swanepoel.CutAllocation
@[expose] public section
set_option autoImplicit false

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem TrackSystem.cut_crossings_image (D E : TrackSystem) (A B : Finset D.Track)
    (f : D.Track→E.Track) (hf : Function.Injective f)
    (hAdj : ∀ u v,E.crossing.Adj (f u) (f v) ↔ D.crossing.Adj u v) :
    E.crossings (A.image f) (B.image f)=D.crossings A B := by
  unfold TrackSystem.crossings
  symm
  refine Finset.card_bij (fun p _ => (f p.1,f p.2)) ?_ ?_ ?_
  · intro p hp
    have h := Finset.mem_filter.mp hp
    have hm := Finset.mem_product.mp h.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨p.1,hm.1,rfl⟩,Finset.mem_image.mpr ⟨p.2,hm.2,rfl⟩⟩,
      (hAdj p.1 p.2).mpr h.2⟩
  · intro p _ q _ hpq
    exact Prod.ext (hf (congrArg Prod.fst hpq)) (hf (congrArg Prod.snd hpq))
  · intro q hq
    have h := Finset.mem_filter.mp hq
    obtain ⟨u,hu,huq⟩ := Finset.mem_image.mp (Finset.mem_product.mp h.1).1
    obtain ⟨v,hv,hvq⟩ := Finset.mem_image.mp (Finset.mem_product.mp h.1).2
    refine ⟨(u,v),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu,hv⟩,?_⟩,
      Prod.ext huq hvq⟩
    exact (hAdj u v).mp (by simpa only [huq,hvq] using h.2)

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

theorem canonicalInheritedNonAnchors_subset (ht : G.TriangleFree) (side : Bool) :
    B.canonicalInheritedNonAnchors ht side⊆(B.canonicalHalfSystem ht side).nonAnchorCrossers := by
  intro u hu
  have h := Finset.mem_filter.mp hu
  exact Finset.mem_filter.mpr ⟨h.1,h.2.1⟩

theorem inheritedNonAnchorCrossings_eq_sum (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool) :
    B.inheritedNonAnchorCrossings ht side=
      ∑ u∈B.canonicalInheritedNonAnchors ht side,(B.canonicalHalfTracks ht side).s u := by
  let H := B.canonicalHalfTracks ht side
  let D := componentSystem G ht ∅ 0
  let E := Fintype.equivFin (TrackComponent G)
  let f : H.Track→D.Track := fun u => E (B.canonicalHalfComponent ht side u)
  have hf : Function.Injective f := E.injective.comp
    ((B.halfComponentMap_injective ht side).comp
      (Fintype.equivFin (TrackComponent (B.halfGraph side))).symm.injective)
  have hAdj : ∀ u v,D.crossing.Adj (f u) (f v) ↔ H.crossing.Adj u v := by
    intro u v
    change ComponentCrosses (E.symm (f u)) (E.symm (f v)) ↔ _
    simp only [f,Equiv.symm_apply_apply]
    exact (B.halfComponentMap_crossing_iff ht side _ _).symm
  have hI : (B.canonicalInheritedNonAnchors ht side).image f=
      G.componentIndices (B.inheritedNonAnchors ht side) := by
    unfold PennyGraph.componentIndices
    rw [Finset.map_eq_image]
    change (B.canonicalInheritedNonAnchors ht side).image
      (E ∘ B.canonicalHalfComponent ht side)=_
    rw [← Finset.image_image,B.canonicalInheritedNonAnchors_image ht hc hcut side]
    rfl
  have hA : H.terminal.image f=G.componentIndices (B.bankAnchorTracks ht side) := by
    unfold PennyGraph.componentIndices
    rw [Finset.map_eq_image]
    change H.terminal.image (E ∘ B.canonicalHalfComponent ht side)=_
    rw [← Finset.image_image,B.canonicalHalf_anchors_image ht hc hcut side]
    rfl
  have h := H.cut_crossings_image D (B.canonicalInheritedNonAnchors ht side) H.terminal f hf hAdj
  rw [hI,hA] at h
  exact h.trans (H.crossings_sum _ _)

theorem terminalCutCrossers_card_eq_s (ht : G.TriangleFree) :
    B.terminalCutCrossers.card=
      (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).s
        (Fintype.equivFin (TrackComponent G) cut) := by
  let E := Fintype.equivFin (TrackComponent G)
  have hfilter :
      (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).terminal.filter
        ((componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).crossing.Adj (E cut))=
      G.componentIndices B.terminalCutCrossers := by
    change (((Finset.univ : Finset (Fin (Fintype.card (TrackComponent G))))\
      G.ordinaryTrackComponents.map E.toEmbedding).filter
        (fun i => ComponentCrosses (E.symm (E cut)) (E.symm i)))=_
    ext i
    simp only [Finset.mem_filter,Finset.mem_sdiff,Finset.mem_univ,true_and,
      Finset.mem_map_equiv,G.mem_componentIndices,terminalCutCrossers,
      G.mem_terminalTrackComponents,E.symm_apply_apply]
    rfl
  have hcard := congrArg Finset.card hfilter
  have hmap : (G.componentIndices B.terminalCutCrossers).card=B.terminalCutCrossers.card :=
    Finset.card_map _
  exact (hcard.trans hmap).symm

theorem canonical_cut_sum_allocation (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) :
    ((componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).r : ℤ)+G.faceDefectCount ht=
      ((B.canonicalHalfSystem ht false).R+
        ∑ u∈B.canonicalInheritedNonAnchors ht false,((B.canonicalHalfTracks ht false).s u : ℤ))+
      ((B.canonicalHalfSystem ht true).R+
        ∑ u∈B.canonicalInheritedNonAnchors ht true,((B.canonicalHalfTracks ht true).s u : ℤ)) := by
  rw [B.canonical_cut_R_allocation ht hc hcut,
    B.inheritedNonAnchorCrossings_eq_sum ht hc hcut false,
    B.inheritedNonAnchorCrossings_eq_sum ht hc hcut true]
  simp only [Nat.cast_sum]
  ring

theorem canonical_cut_conservation (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) :
    (B.canonicalHalfSystem ht false).k+(B.canonicalHalfSystem ht true).k=
        (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).K+
          (B.splitTerminalJoins ht).card ∧
    (B.canonicalHalfSystem ht false).d+(B.canonicalHalfSystem ht true).d=
        (B.terminalCutCrossers.card : ℤ)+(B.splitTerminalJoins ht).card ∧
    (∀ side : Bool,(B.canonicalHalfSystem ht side).d+
        (B.canonicalInheritedNonAnchors ht side).card=(B.terminalCutCrossers.card : ℤ)) := by
  have hK := B.bank_K_conservation ht
  have hD := B.bank_meeting_count_conservation ht hcut
  have hL := B.bank_meeting_nonanchor_count ht false
  have hR := B.bank_meeting_nonanchor_count ht true
  have kL := (B.canonicalHalfBankRealization ht hc hcut false).k_eq_bankK
  have kR := (B.canonicalHalfBankRealization ht hc hcut true).k_eq_bankK
  have dL := (B.canonicalHalfBankRealization ht hc hcut false).d_eq_bankMeetingAnchors
  have dR := (B.canonicalHalfBankRealization ht hc hcut true).d_eq_bankMeetingAnchors
  refine ⟨by rw [kL,kR]; exact hK,by rw [dL,dR]; omega,?_⟩
  intro side
  rw [B.canonicalInheritedNonAnchors_card ht hc hcut side]
  cases side <;> omega

theorem inheritedNonAnchorCrossings_le (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool) :
    (B.inheritedNonAnchorCrossings ht side : ℤ)≤
      (B.inheritedNonAnchors ht side).card*((B.canonicalHalfSystem ht side).k-(B.canonicalHalfSystem ht side).d) := by
  rw [B.inheritedNonAnchorCrossings_eq_sum ht hc hcut side,Nat.cast_sum]
  have hb := (B.canonicalHalfBankRealization ht hc hcut side).nonAnchorBound hdegree hcut
  calc
    _≤∑ _u∈B.canonicalInheritedNonAnchors ht side,
        ((B.canonicalHalfSystem ht side).k-(B.canonicalHalfSystem ht side).d) := by
      apply Finset.sum_le_sum
      intro u hu
      exact hb u (B.canonicalInheritedNonAnchors_subset ht side hu)
    _=_ := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      rw [B.canonicalInheritedNonAnchors_card ht hc hcut side]

end OrdinaryCutBanks
end Swanepoel
