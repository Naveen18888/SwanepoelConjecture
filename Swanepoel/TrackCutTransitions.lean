module
public import Swanepoel.TrackCut
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def cutRhombus {n : ℕ} {G : PennyGraph n} (cut : TrackComponent G) (R : RhombusSet G) : Prop :=
  edgeComponent R.representative.edgeAB=cut ∨ edgeComponent R.representative.edgeAD=cut

def TrackCutStep {n : ℕ} {G : PennyGraph n} (cut : TrackComponent G)
    (a b : OrientedEdge G) : Prop :=
  ∃ p : SpineTransition G, p.val=(a,b) ∧ ¬cutRhombus cut p.rhombus

theorem TrackCutStep.to_positive {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G}
    {a b : OrientedEdge G} (h : TrackCutStep cut a b) : PositiveCellStep a b := by
  obtain ⟨p,hp,_⟩ := h
  simpa only [hp] using p.property

theorem TrackCutStep.reverse {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G}
    {a b : OrientedEdge G} (h : TrackCutStep cut a b) :
    TrackCutStep cut (reverseEdge b) (reverseEdge a) := by
  obtain ⟨p,hp,hcut⟩ := h
  refine ⟨p.reverse,?_,?_⟩
  · simp only [SpineTransition.reverse,hp]
  · rwa [p.reverse_rhombus]

theorem cutRhombus_pair_eq {n : ℕ} {G : PennyGraph n} (R : RhombusSet G)
    {t u : TrackComponent G} (htu : t≠u) (ht : cutRhombus t R) (hu : cutRhombus u R) :
    R.representative.trackPair=s(t,u) := by
  rcases ht with ht | ht <;> rcases hu with hu | hu
  · exact False.elim (htu (ht.symm.trans hu))
  · simp only [RhombusCell.trackPair,ht,hu]
  · simp only [RhombusCell.trackPair,ht,hu]
    exact Sym2.eq_swap
  · exact False.elim (htu (ht.symm.trans hu))

theorem cutRhombus_of_pair_eq {n : ℕ} {G : PennyGraph n} (R : RhombusSet G)
    {t u : TrackComponent G} (h : R.representative.trackPair=s(t,u)) :
    cutRhombus t R ∧ cutRhombus u R := by
  change s(edgeComponent R.representative.edgeAB,edgeComponent R.representative.edgeAD)=s(t,u) at h
  rcases Sym2.eq_iff.mp h with h | h
  · exact ⟨Or.inl h.1,Or.inr h.2⟩
  · exact ⟨Or.inr h.2,Or.inl h.1⟩

theorem cutRhombus_crosses_component {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    (p : SpineTransition G) {cut : TrackComponent G}
    (hne : edgeComponent p.val.1≠cut) (hcut : cutRhombus cut p.rhombus) :
    ComponentCrosses (edgeComponent p.val.1) cut := by
  have htR : cutRhombus (edgeComponent p.val.1) p.rhombus := (transitionIncidence ht p).property
  have hp := cutRhombus_pair_eq p.rhombus hne htR hcut
  change s(edgeComponent p.rhombus.representative.edgeAB,
    edgeComponent p.rhombus.representative.edgeAD)=s(edgeComponent p.val.1,cut) at hp
  refine ⟨p.rhombus.representative,?_⟩
  exact Sym2.eq_iff.mp hp

theorem noncrossing_step_preserved {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {cut : TrackComponent G} {a b : OrientedEdge G}
    (hne : edgeComponent a≠cut) (hncross : ¬ComponentCrosses (edgeComponent a) cut)
    (hab : PositiveCellStep a b) : TrackCutStep cut a b := by
  let p : SpineTransition G := ⟨(a,b),hab⟩
  exact ⟨p,rfl,fun h => hncross (cutRhombus_crosses_component ht p hne h)⟩

theorem cut_track_step_removed {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {cut : TrackComponent G} {a b : OrientedEdge G} (ha : edgeComponent a=cut) :
    ¬TrackCutStep cut a b := by
  rintro ⟨p,hp,hcut⟩
  have hinc := (transitionIncidence ht p).property
  change cutRhombus (edgeComponent p.val.1) p.rhombus at hinc
  have hcomp : edgeComponent p.val.1=cut := by rw [hp]; exact ha
  exact hcut (by simpa only [hcomp] using hinc)

theorem crossing_cut_transition_pair {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    (t cut : TrackComponent G) (hne : t≠cut) (hcross : ComponentCrosses t cut) :
    ∃ q : SpineTransition G, edgeComponent q.val.1=t ∧ cutRhombus cut q.rhombus ∧
      ∀ p : SpineTransition G,
        (edgeComponent p.val.1=t ∧ cutRhombus cut p.rhombus) ↔ p=q ∨ p=q.reverse := by
  obtain ⟨C,hC⟩ := hcross
  have hCt : edgeComponent C.edgeAB=t ∨ edgeComponent C.edgeAD=t := by tauto
  obtain ⟨a,b,hab,ha,_,hcorners⟩ := C.spineWitness ht t hCt
  let q : SpineTransition G := ⟨(a,b),hab⟩
  have hqcorners : q.rhombus.representative.corners=C.corners := by
    rw [q.rhombus.representative_corners]
    exact hcorners
  have hCpair : C.trackPair=s(t,cut) := by
    rcases hC with hC | hC
    · simp only [RhombusCell.trackPair,hC.1,hC.2]
    · simp only [RhombusCell.trackPair,hC.1,hC.2]
      exact Sym2.eq_swap
  have hqpair : q.rhombus.representative.trackPair=s(t,cut) :=
    (q.rhombus.representative.trackPair_of_corners ht C hqcorners).trans hCpair
  have hqcut := (cutRhombus_of_pair_eq q.rhombus hqpair).2
  refine ⟨q,ha,hqcut,?_⟩
  intro p
  constructor
  · rintro ⟨hp,hpcut⟩
    have hpinc : cutRhombus t p.rhombus := by
      have hinc : cutRhombus (edgeComponent p.val.1) p.rhombus := (transitionIncidence ht p).property
      simpa only [hp] using hinc
    have hppair := cutRhombus_pair_eq p.rhombus hne hpinc hpcut
    have hr : p.rhombus=q.rhombus := by
      apply rhombusCrossingMap_injective G ht
      apply Subtype.ext
      exact hppair.trans hqpair.symm
    exact transition_same_rhombus_component ht p q hr (hp.trans ha.symm)
  · rintro (rfl | rfl)
    · exact ⟨ha,hqcut⟩
    · exact ⟨q.reverse_component.trans ha,by rwa [q.reverse_rhombus]⟩

theorem crossing_cut_transition_count {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    (t cut : TrackComponent G) (hne : t≠cut) (hcross : ComponentCrosses t cut) :
    ((Finset.univ : Finset (SpineTransition G)).filter
      (fun p => edgeComponent p.val.1=t ∧ cutRhombus cut p.rhombus)).card=2 := by
  obtain ⟨q,_,_,hall⟩ := crossing_cut_transition_pair ht t cut hne hcross
  have hset : ((Finset.univ : Finset (SpineTransition G)).filter
      (fun p => edgeComponent p.val.1=t ∧ cutRhombus cut p.rhombus))={q,q.reverse} := by
    ext p
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton] using hall p
  rw [hset,Finset.card_pair q.reverse_ne]

end Swanepoel
