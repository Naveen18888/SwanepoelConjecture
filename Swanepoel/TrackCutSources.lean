module
public import Swanepoel.TrackCutCounting
public import Swanepoel.TerminalPortConservation
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def TrackCutSource {n : ℕ} {G : PennyGraph n} (cut : TrackComponent G) (a : OrientedEdge G) : Prop :=
  ¬∃ b, TrackCutStep cut b a

def trackCutSources {n : ℕ} {G : PennyGraph n} (cut c : TrackComponent G) : Finset (OrientedEdge G) :=
  Finset.univ.filter (fun a => TrackCutSource cut a ∧ edgeComponent a=c)

def originalTrackSources {n : ℕ} {G : PennyGraph n} (c : TrackComponent G) : Finset (OrientedEdge G) :=
  Finset.univ.filter (fun a => SpineSource a ∧ edgeComponent a=c)

theorem trackCutSource_iff {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    (cut : TrackComponent G) (a : OrientedEdge G) :
    TrackCutSource cut a ↔ SpineSource a ∨
      ∃ p : SpineTransition G, p.val.2=a ∧ cutRhombus cut p.rhombus := by
  constructor
  · intro ha
    by_cases hsource : SpineSource a
    · exact Or.inl hsource
    · obtain ⟨b,hba⟩ := not_not.mp hsource
      let p : SpineTransition G := ⟨(b,a),hba⟩
      refine Or.inr ⟨p,rfl,?_⟩
      by_contra hn
      exact ha ⟨b,p,rfl,hn⟩
  · rintro (ha | ⟨p,hp,hcut⟩)
    · rintro ⟨b,hba⟩
      exact ha ⟨b,hba.to_positive⟩
    · rintro ⟨b,q,hq,hnot⟩
      have htarget : p.val.2=q.val.2 := hp.trans (congrArg Prod.snd hq).symm
      have hqpos : PositiveCellStep q.val.1 p.val.2 := by rw [htarget]; exact q.property
      have hsource := positive_step_injective ht p.property hqpos
      have hpq : p=q := Subtype.ext (Prod.ext hsource htarget)
      exact hnot (hpq ▸ hcut)

theorem removed_transition_target_fresh {n : ℕ} {G : PennyGraph n}
    (p : SpineTransition G) : ¬SpineSource p.val.2 := fun h => h ⟨p.val.1,p.property⟩

theorem crossing_cut_sources_eq {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    (c cut : TrackComponent G) (hne : c≠cut) (hcross : ComponentCrosses c cut) :
    ∃ q : SpineTransition G, edgeComponent q.val.1=c ∧ cutRhombus cut q.rhombus ∧
      trackCutSources cut c=originalTrackSources c ∪ {q.val.2,reverseEdge q.val.1} := by
  obtain ⟨q,hqc,hqcut,hpairs⟩ := crossing_cut_transition_pair ht c cut hne hcross
  refine ⟨q,hqc,hqcut,?_⟩
  ext a
  simp only [trackCutSources,originalTrackSources,Finset.mem_filter,Finset.mem_univ,
    true_and,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨ha,hac⟩
    rcases (trackCutSource_iff ht cut a).mp ha with hold | ⟨p,hpa,hpcut⟩
    · exact Or.inl ⟨hold,hac⟩
    · have hpc : edgeComponent p.val.1=c :=
        (positive_path_component (Relation.ReflTransGen.single p.property)).trans (hpa ▸ hac)
      rcases (hpairs p).mp ⟨hpc,hpcut⟩ with rfl | rfl
      · exact Or.inr (Or.inl hpa.symm)
      · exact Or.inr (Or.inr hpa.symm)
  · rintro (⟨hold,hac⟩ | rfl | rfl)
    · exact ⟨(trackCutSource_iff ht cut a).mpr (Or.inl hold),hac⟩
    · exact ⟨(trackCutSource_iff ht cut q.val.2).mpr (Or.inr ⟨q,rfl,hqcut⟩),
        (positive_path_component (Relation.ReflTransGen.single q.property)).symm.trans hqc⟩
    · exact ⟨(trackCutSource_iff ht cut (reverseEdge q.val.1)).mpr
        (Or.inr ⟨q.reverse,rfl,by rwa [q.reverse_rhombus]⟩),
        (reverse_component q.val.1).symm.trans hqc⟩

theorem crossing_cut_fresh_source_count {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    (c cut : TrackComponent G) (hne : c≠cut) (hcross : ComponentCrosses c cut) :
    (trackCutSources cut c \ originalTrackSources c).card=2 ∧
      (trackCutSources cut c).card=4 := by
  obtain ⟨q,hqc,_,hset⟩ := crossing_cut_sources_eq ht c cut hne hcross
  have hends : q.val.2≠reverseEdge q.val.1 := by
    intro he
    have hh := congrArg reverseEdge he
    simp only [reverseEdge_involutive] at hh
    exact spine_opposite_sources_ne (Relation.ReflTransGen.single q.property) hh.symm
  have hdis : Disjoint (originalTrackSources c) {q.val.2,reverseEdge q.val.1} := by
    apply Finset.disjoint_right.mpr
    intro a ha hold
    have hs := (Finset.mem_filter.mp hold).2.1
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact removed_transition_target_fresh q hs
    · exact removed_transition_target_fresh q.reverse hs
  have hold : (originalTrackSources c).card=2 := component_source_count ht c
  constructor
  · rw [hset,Finset.union_sdiff_left,Finset.sdiff_eq_self_of_disjoint hdis.symm,Finset.card_pair hends]
  · rw [hset,Finset.card_union_of_disjoint hdis,hold,Finset.card_pair hends]

theorem noncrossing_cut_sources_eq {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    (c cut : TrackComponent G) (hne : c≠cut) (hncross : ¬ComponentCrosses c cut) :
    trackCutSources cut c=originalTrackSources c := by
  ext a
  simp only [trackCutSources,originalTrackSources,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨ha,hac⟩
    refine ⟨?_,hac⟩
    rintro ⟨b,hba⟩
    have hbc : edgeComponent b=c := (positive_path_component (Relation.ReflTransGen.single hba)).trans hac
    exact ha ⟨b,noncrossing_step_preserved ht (by simpa only [hbc] using hne)
      (by simpa only [hbc] using hncross) hba⟩
  · rintro ⟨ha,hac⟩
    exact ⟨(trackCutSource_iff ht cut a).mpr (Or.inl ha),hac⟩

theorem cut_bank_end_centres {n : ℕ} {G : PennyGraph n} (q : SpineTransition G) :
    ∃ C : RhombusCell G,
      edgeCenter q.val.2=RhombusCell.midpoint2 (G.point C.d) (G.point C.c) ∧
      edgeCenter (reverseEdge q.val.1)=RhombusCell.midpoint2 (G.point C.a) (G.point C.b) ∧
      stepCenter q.val.1 q.val.2=C.center := by
  obtain ⟨C,he,hf,_⟩ := q.property
  refine ⟨C,?_,?_,?_⟩
  · simp only [edgeCenter,hf]
  · rw [edgeCenter_reverse]
    simp only [edgeCenter,he]
  · have heq : q.val.1=C.edgeAB := Subtype.ext he
    have hfq : q.val.2=C.edgeDC := Subtype.ext hf
    rw [heq,hfq,C.stepCenter_eq]

theorem complete_spine_original_sources {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {s t : OrientedEdge G} (hs : ¬∃g, PositiveCellStep g s)
    (htop : ¬∃g, PositiveCellStep t g) (hst : Relation.ReflTransGen PositiveCellStep s t) :
    originalTrackSources (edgeComponent s)={s,reverseEdge t} := by
  have hrt : SpineSource (reverseEdge t) := by
    rintro ⟨g,hg⟩
    have hh := hg.reverse
    simp only [reverseEdge_involutive] at hh
    exact htop ⟨reverseEdge g,hh⟩
  have hrtc : edgeComponent (reverseEdge t)=edgeComponent s :=
    (reverse_component t).symm.trans (positive_path_component hst).symm
  have hsub : ({s,reverseEdge t} : Finset (OrientedEdge G))⊆originalTrackSources (edgeComponent s) := by
    intro e he
    simp only [Finset.mem_insert,Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs,rfl⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hrt,hrtc⟩
  have hc : (originalTrackSources (edgeComponent s)).card=2 := component_source_count ht _
  exact (Finset.eq_of_subset_of_card_le hsub (by
    rw [hc,Finset.card_pair (spine_opposite_sources_ne hst)])).symm

theorem PennyGraph.complete_spine_terminal_iff {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    {s t : OrientedEdge G} (hs : ¬∃g, PositiveCellStep g s)
    (htop : ¬∃g, PositiveCellStep t g) (hst : Relation.ReflTransGen PositiveCellStep s t) :
    edgeComponent s∈G.terminalTrackComponents ↔
      Bornology.IsBounded (G.sourceFace s).val ∨
        Bornology.IsBounded (G.sourceFace (reverseEdge t)).val := by
  have hends := complete_spine_original_sources ht hs htop hst
  rw [G.terminal_iff_bounded_source]
  constructor
  · rintro ⟨e,he,hec,hb⟩
    have hmem : e∈originalTrackSources (edgeComponent s) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,he,hec⟩
    rw [hends] at hmem
    simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl
    · exact Or.inl hb
    · exact Or.inr hb
  · rintro (hb | hb)
    · exact ⟨s,hs,rfl,hb⟩
    · have hmem : reverseEdge t∈originalTrackSources (edgeComponent s) := by rw [hends]; simp
      have hp := (Finset.mem_filter.mp hmem).2
      exact ⟨reverseEdge t,hp.1,hp.2,hb⟩

theorem PennyGraph.complete_spine_join_iff {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    {s t : OrientedEdge G} (hs : ¬∃g, PositiveCellStep g s)
    (htop : ¬∃g, PositiveCellStep t g) (hst : Relation.ReflTransGen PositiveCellStep s t) :
    edgeComponent s∈G.terminalJoinTrackComponents ↔
      Bornology.IsBounded (G.sourceFace s).val ∧
        Bornology.IsBounded (G.sourceFace (reverseEdge t)).val := by
  have hends := complete_spine_original_sources ht hs htop hst
  have hrtMem : reverseEdge t∈originalTrackSources (edgeComponent s) := by rw [hends]; simp
  have hrt := (Finset.mem_filter.mp hrtMem).2
  rw [G.terminalJoin_iff_all_ends_defect ht]
  constructor
  · rintro ⟨_,hall⟩
    exact ⟨G.defectPlaneFace_isBounded ht (hall s hs rfl),
      G.defectPlaneFace_isBounded ht (hall (reverseEdge t) hrt.1 hrt.2)⟩
  · rintro ⟨hbS,hbT⟩
    refine ⟨(G.complete_spine_terminal_iff ht hs htop hst).mpr (Or.inl hbS),?_⟩
    intro e he hec
    have hem : e∈originalTrackSources (edgeComponent s) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,he,hec⟩
    rw [hends] at hem
    simp only [Finset.mem_insert,Finset.mem_singleton] at hem
    rcases hem with rfl | rfl
    · exact (G.sourceFace_defect_or_unbounded ht _ he).resolve_right (fun hn => hn hbS)
    · exact (G.sourceFace_defect_or_unbounded ht (reverseEdge t) he).resolve_right (fun hn => hn hbT)

def PennyGraph.cutTerminalPieces {n : ℕ} (G : PennyGraph n) (cut : TrackComponent G)
    (s t : OrientedEdge G) : Finset (TrackCutComponent cut) :=
  (if Bornology.IsBounded (G.sourceFace s).val then {trackCutComponent cut s} else ∅) ∪
    (if Bornology.IsBounded (G.sourceFace (reverseEdge t)).val then {trackCutComponent cut t} else ∅)

theorem PennyGraph.cutTerminalPieces_count {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    {cut : TrackComponent G} {s t : OrientedEdge G}
    (hs : ¬∃g, PositiveCellStep g s) (htop : ¬∃g, PositiveCellStep t g)
    (hst : Relation.ReflTransGen PositiveCellStep s t)
    (hsep : ComponentCrosses (edgeComponent s) cut → trackCutComponent cut s≠trackCutComponent cut t)
    (hsame : ¬ComponentCrosses (edgeComponent s) cut → trackCutComponent cut s=trackCutComponent cut t) :
    (G.cutTerminalPieces cut s t).card=
      (if edgeComponent s∈G.terminalTrackComponents then 1 else 0)+
        (if ComponentCrosses (edgeComponent s) cut ∧ edgeComponent s∈G.terminalJoinTrackComponents
          then 1 else 0) := by
  have hterm := G.complete_spine_terminal_iff ht hs htop hst
  have hjoin := G.complete_spine_join_iff ht hs htop hst
  by_cases hcross : ComponentCrosses (edgeComponent s) cut
  · have hne := hsep hcross
    by_cases hS : Bornology.IsBounded (G.sourceFace s).val <;>
      by_cases hT : Bornology.IsBounded (G.sourceFace (reverseEdge t)).val <;>
      simp [PennyGraph.cutTerminalPieces,hterm,hjoin,hS,hT,hcross,hne]
  · have heq := hsame hcross
    by_cases hS : Bornology.IsBounded (G.sourceFace s).val <;>
      by_cases hT : Bornology.IsBounded (G.sourceFace (reverseEdge t)).val <;>
      simp [PennyGraph.cutTerminalPieces,hterm,hjoin,hS,hT,hcross,heq]

theorem track_cut_spine_endpoint_realization {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    (c cut : TrackComponent G) (hne : c≠cut) : ∃ s t : OrientedEdge G,
      edgeComponent s=c ∧ (¬∃g, PositiveCellStep g s) ∧ (¬∃g, PositiveCellStep t g) ∧
      Relation.ReflTransGen PositiveCellStep s t ∧
      (ComponentCrosses c cut → trackCutComponent cut s≠trackCutComponent cut t) ∧
      (¬ComponentCrosses c cut → trackCutComponent cut s=trackCutComponent cut t) := by
  by_cases hcross : ComponentCrosses c cut
  · obtain ⟨q,hqc,hqcut,hpairs⟩ := crossing_cut_transition_pair ht c cut hne hcross
    obtain ⟨s,t,hs,htop,he,_⟩ := component_spine_iff ht q.val.1
    have hft := spine_suffix_closed ht htop he.2 q.property
    have hpairs' : ∀ p : SpineTransition G,
        edgeComponent p.val.1=edgeComponent q.val.1 ∧ cutRhombus cut p.rhombus → p=q ∨ p=q.reverse := by
      intro p hp
      exact (hpairs p).mp ⟨hp.1.trans hqc,hp.2⟩
    have hlocal : ∀ a b, OnSpine s t a →
        (TrackCutStep cut a b ↔ PositiveSpineCutStep q.val.1 q.val.2 a b) :=
      fun a b ha => trackCutStep_on_spine_iff ht cut q hqcut hpairs' he.1 (a := a) (b := b) ha
    refine ⟨s,t,(positive_path_component he.1).trans hqc,hs,htop,he.1.trans he.2,?_,?_⟩
    · intro _ hsame
      have hpath := trackCut_component_to_local ht hs htop hlocal (Quotient.exact hsame)
        ⟨Relation.ReflTransGen.refl,he.1.trans he.2⟩
      have hte := (cut_component_predecessor_iff ht q.property hpath).mp he.1
      exact no_closed_positive_spine q.val.1 (Relation.TransGen.head' q.property (hft.trans hte))
    · exact fun hn => False.elim (hn hcross)
  · obtain ⟨s,t,hsc,hs,htop,hst,_,_⟩ := noncrossing_track_cut_realization ht c cut hne hcross
    refine ⟨s,t,hsc,hs,htop,hst,fun hc => False.elim (hcross hc),?_⟩
    intro _
    apply Quotient.sound
    exact Relation.EqvGen.reflTransGen_le_eqvGen _ _ _
      (noncrossing_path_preserved ht (by simpa only [hsc] using hne)
        (by simpa only [hsc] using hcross) hst)

theorem PennyGraph.cut_terminal_piece_conservation {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (cut : TrackComponent G) (hordinary : cut∈G.ordinaryTrackComponents) :
    ∃ s t : TrackCutOther cut → OrientedEdge G,
      (∀ c, edgeComponent (s c)=c.val ∧
        (¬∃g, PositiveCellStep g (s c)) ∧ (¬∃g, PositiveCellStep (t c) g) ∧
        Relation.ReflTransGen PositiveCellStep (s c) (t c)) ∧
      (∑ c : TrackCutOther cut, (G.cutTerminalPieces cut (s c) (t c)).card)=
        G.terminalTrackComponents.card+
          ((Finset.univ : Finset (TrackCutOther cut)).filter
            (fun c => ComponentCrosses c.val cut ∧ c.val∈G.terminalJoinTrackComponents)).card := by
  classical
  have hex := fun c : TrackCutOther cut => track_cut_spine_endpoint_realization ht c.val cut c.property
  choose s t h using hex
  refine ⟨s,t,fun c => ⟨(h c).1,(h c).2.1,(h c).2.2.1,(h c).2.2.2.1⟩,?_⟩
  have hp : ∀ c : TrackCutOther cut,
      (G.cutTerminalPieces cut (s c) (t c)).card=
        (if c.val∈G.terminalTrackComponents then 1 else 0)+
          (if ComponentCrosses c.val cut ∧ c.val∈G.terminalJoinTrackComponents then 1 else 0) := by
    intro c
    have hc := (h c).1
    simpa only [hc] using G.cutTerminalPieces_count ht (h c).2.1 (h c).2.2.1 (h c).2.2.2.1
      (by simpa only [hc] using (h c).2.2.2.2.1)
      (by simpa only [hc] using (h c).2.2.2.2.2)
  have hnot : cut∉G.terminalTrackComponents :=
    fun hcut => (G.mem_terminalTrackComponents cut).mp hcut hordinary
  have htermcard :
      ((Finset.univ : Finset (TrackCutOther cut)).filter
        (fun c => c.val∈G.terminalTrackComponents)).card=G.terminalTrackComponents.card := by
    refine Finset.card_bij (fun c _ => c.val) ?_ ?_ ?_
    · intro c hc
      exact (Finset.mem_filter.mp hc).2
    · intro c _ d _ hcd
      exact Subtype.ext hcd
    · intro c hc
      have hne : c≠cut := fun hh => hnot (hh ▸ hc)
      exact ⟨⟨c,hne⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩,rfl⟩
  have hterm : (∑ c : TrackCutOther cut, (if c.val∈G.terminalTrackComponents then 1 else 0))=
      G.terminalTrackComponents.card := by
    rw [← htermcard]
    simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  have hjoin : (∑ c : TrackCutOther cut,
      (if ComponentCrosses c.val cut ∧ c.val∈G.terminalJoinTrackComponents then 1 else 0))=
      ((Finset.univ : Finset (TrackCutOther cut)).filter
        (fun c => ComponentCrosses c.val cut ∧ c.val∈G.terminalJoinTrackComponents)).card := by
    simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  calc
    _ = ∑ c : TrackCutOther cut,
        ((if c.val∈G.terminalTrackComponents then 1 else 0)+
          (if ComponentCrosses c.val cut ∧ c.val∈G.terminalJoinTrackComponents then 1 else 0)) :=
      Finset.sum_congr rfl (fun c _ => hp c)
    _ = _ := by rw [Finset.sum_add_distrib,hterm,hjoin]

end Swanepoel
