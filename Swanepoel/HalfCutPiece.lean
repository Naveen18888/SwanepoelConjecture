module
public import Swanepoel.HalfPieceLocation
public import Swanepoel.TwoSpineTransport
@[expose] public section

noncomputable section
namespace Swanepoel
open Set

theorem PositiveSpineChain.onSpine_center_mem_trace {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {s t a : OrientedEdge G} (p : PositiveSpineChain G s t)
    (ha : OnSpine s t a) : edgeCenter a∈p.toPlane.trace := by
  induction p with
  | nil s => rw [onSpine_refl_eq ha]; exact Set.mem_singleton _
  | cons s b t hsb tail ih =>
    by_cases heq : a=s
    · rw [heq]
      exact Or.inl (left_mem_segment ℝ _ _)
    · rcases ha.1.cases_head with h | ⟨c,hsc,hca⟩
      · exact False.elim (heq h.symm)
      · have hbc := positive_step_functional ht hsb hsc
        exact Or.inr (ih ⟨by simpa only [hbc] using hca,ha.2⟩)

structure HalfCutPiece {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G}
    (B : OrdinaryCutBanks G cut) (ht : G.TriangleFree) (side : Bool) (v : TrackComponent G) where
  start : OrientedEdge G
  finish : OrientedEdge G
  component : edgeComponent start=v
  source : SpineSource start
  sink : ¬∃a,PositiveCellStep finish a
  exterior : ¬Bornology.IsBounded (G.sourceFace start).val
  source_code : B.cutPieceBankCode ht (trackCutComponent cut start)=side
  crossing : SpineTransition G
  removed : cutRhombus cut crossing.rhombus
  before : Relation.ReflTransGen PositiveCellStep start crossing.val.1
  after : Relation.ReflTransGen PositiveCellStep crossing.val.2 finish
  unique_removed : ∀ p : SpineTransition G,
    (edgeComponent p.val.1=edgeComponent crossing.val.1 ∧ cutRhombus cut p.rhombus) ↔
      p=crossing ∨ p=crossing.reverse
  chain : MaskedSpineChain G cut start crossing.val.1

theorem OrdinaryCutBanks.exists_nonanchor_halfCutPiece {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)
    (side : Bool) (v : TrackComponent G) (hcross : ComponentCrosses v cut)
    (hnot : v∉B.bankAnchorTracks ht side) : Nonempty (HalfCutPiece B ht side v) := by
  obtain ⟨e,he,hev,heCode,hext⟩ := B.exists_nonanchor_exterior_source ht side v hcross hnot
  have hne : edgeComponent e≠cut := hev ▸ (componentGraph G ht).ne_of_adj hcross
  obtain ⟨q,hqcut,hprefix,hpairs⟩ := crossing_cut_transition_before_source ht cut e he hne (hev ▸ hcross)
  obtain ⟨s,t,hs,htop,hE,hall⟩ := component_spine_iff ht e
  have hse : s=e := source_path_eq he hE.1
  subst s
  have heq : OnSpine e t q.val.1 :=
    (onSpine_positive_path_iff ht hs htop hprefix).mp ⟨Relation.ReflTransGen.refl,hE.1.trans hE.2⟩
  have hsuffix := spine_suffix_closed ht htop heq.2 q.property
  obtain ⟨p⟩ := MaskedSpineChain.exists_of_reach (path_before_global_cut_preserved cut q hpairs hprefix)
  exact ⟨⟨e,t,hev,he,htop,hext,heCode,q,hqcut,hprefix,hsuffix,hpairs,p⟩⟩

namespace HalfCutPiece
variable {n : ℕ} {G : PennyGraph n} {cut v : TrackComponent G}
    {B : OrdinaryCutBanks G cut} {ht : G.TriangleFree} {side : Bool}
    (P : HalfCutPiece B ht side v)

theorem full_reach : Relation.ReflTransGen PositiveCellStep P.start P.finish :=
  (P.before.tail P.crossing.property).trans P.after

theorem midpoint_mem_of_code (hne : v≠cut) (e : OrientedEdge G)
    (he : edgeComponent e=v)
    (hcode : B.cutPieceBankCode ht (trackCutComponent cut e)=side) :
    edgeCenter e∈P.chain.positive.toPlane.trace := by
  obtain ⟨s,t,hs,htop,hE,hall⟩ := component_spine_iff ht P.start
  have hss : s=P.start := source_path_eq P.source hE.1
  subst s
  have hts : t=P.finish := by
    have hreach := (onSpine_positive_path_iff ht P.source htop P.full_reach).mp
      ⟨Relation.ReflTransGen.refl,hE.1.trans hE.2⟩
    rcases hreach.2.cases_head with heq | ⟨a,hfa,_⟩
    · exact heq.symm
    · exact False.elim (P.sink ⟨a,hfa⟩)
  subst t
  have hec : edgeComponent e=edgeComponent P.start := he.trans P.component.symm
  have hns : edgeComponent P.start≠cut := fun h => hne (P.component.symm.trans h)
  rcases (hall e).mp hec with ha | ha
  · have hp := B.same_bank_onSpine_before_cut ht side P.source P.sink P.crossing P.removed
      P.unique_removed P.before P.after ha hns P.source_code hcode
    exact P.chain.positive.onSpine_center_mem_trace ht hp
  · have hrcode : B.cutPieceBankCode ht (trackCutComponent cut (reverseEdge e))=side :=
      (B.cutPieceBankCode_reverse ht e (he ▸ hne)).trans hcode
    have hp := B.same_bank_onSpine_before_cut ht side P.source P.sink P.crossing P.removed
      P.unique_removed P.before P.after (onSpine_reverse_iff.mp ha) hns P.source_code hrcode
    simpa only [edgeCenter_reverse] using P.chain.positive.onSpine_center_mem_trace ht hp

end HalfCutPiece
end Swanepoel
