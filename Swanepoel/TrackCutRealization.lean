module
public import Swanepoel.TrackCutTransitions
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

abbrev TrackCutComponent {n : ℕ} {G : PennyGraph n} (cut : TrackComponent G) :=
  Quotient (Relation.EqvGen.setoid (TrackCutStep cut))

def trackCutComponent {n : ℕ} {G : PennyGraph n} (cut : TrackComponent G) (a : OrientedEdge G) :
    TrackCutComponent cut := Quotient.mk _ a

def trackCutPieces {n : ℕ} {G : PennyGraph n} (cut : TrackComponent G) (s t : OrientedEdge G) :
    Finset (TrackCutComponent cut) := (spineVertices s t).image (trackCutComponent cut)

theorem common_positive_paths_not_reverse {n : ℕ} {G : PennyGraph n}
    {s a b : OrientedEdge G} (ha : Relation.ReflTransGen PositiveCellStep s a)
    (hb : Relation.ReflTransGen PositiveCellStep s b) : a≠reverseEdge b := by
  intro hab
  have hv := (positive_path_vector_eq ha).symm.trans (positive_path_vector_eq hb)
  rw [hab,reverseEdge_vector] at hv
  have hz : carriedVector b=0 := by
    ext i
    have hi := congrArg (fun v : Plane => v i) hv
    change -(carriedVector b i)=carriedVector b i at hi
    change carriedVector b i=0
    linarith
  have hn := carriedVector_norm b
  rw [hz,norm_zero] at hn
  norm_num at hn

theorem trackCutStep_on_spine_iff {n : ℕ} {G : PennyGraph n} (_ht : G.TriangleFree)
    (cut : TrackComponent G) (q : SpineTransition G) (hqcut : cutRhombus cut q.rhombus)
    (hpairs : ∀ p : SpineTransition G,
      edgeComponent p.val.1=edgeComponent q.val.1 ∧ cutRhombus cut p.rhombus → p=q ∨ p=q.reverse)
    {s t a b : OrientedEdge G} (hse : Relation.ReflTransGen PositiveCellStep s q.val.1)
    (ha : OnSpine s t a) :
    TrackCutStep cut a b ↔ PositiveSpineCutStep q.val.1 q.val.2 a b := by
  constructor
  · intro hab
    refine ⟨hab.to_positive,?_⟩
    rintro ⟨rfl,rfl⟩
    obtain ⟨p,hp,hnot⟩ := hab
    have hpq : p=q := Subtype.ext hp
    exact hnot (hpq.symm ▸ hqcut)
  · intro hab
    let p : SpineTransition G := ⟨(a,b),hab.1⟩
    refine ⟨p,rfl,?_⟩
    intro hpcut
    have hcomp : edgeComponent p.val.1=edgeComponent q.val.1 :=
      (positive_path_component ha.1).symm.trans (positive_path_component hse)
    rcases hpairs p ⟨hcomp,hpcut⟩ with hp | hp
    · have hval := congrArg Subtype.val hp
      exact hab.2 ⟨congrArg Prod.fst hval,congrArg Prod.snd hval⟩
    · have heq : a=reverseEdge q.val.2 := congrArg (fun p : SpineTransition G => p.val.1) hp
      exact common_positive_paths_not_reverse ha.1 (hse.tail q.property) heq

theorem onSpine_positive_path_iff {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {s t a b : OrientedEdge G} (hs : ¬∃g, PositiveCellStep g s)
    (htop : ¬∃g, PositiveCellStep t g) (hab : Relation.ReflTransGen PositiveCellStep a b) :
    OnSpine s t a ↔ OnSpine s t b := by
  induction hab with
  | refl => rfl
  | tail _ h ih => exact ih.trans (onSpine_positive_iff ht hs htop h)

theorem onSpine_trackCut_component_iff {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {cut : TrackComponent G} {s t a b : OrientedEdge G} (hs : ¬∃g, PositiveCellStep g s)
    (htop : ¬∃g, PositiveCellStep t g) (hab : Relation.EqvGen (TrackCutStep cut) a b) :
    OnSpine s t a ↔ OnSpine s t b := by
  induction hab with
  | rel _ _ h => exact onSpine_positive_iff ht hs htop h.to_positive
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem trackCut_component_to_local {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {cut : TrackComponent G} {s t e f a b : OrientedEdge G}
    (hs : ¬∃g, PositiveCellStep g s) (htop : ¬∃g, PositiveCellStep t g)
    (hlocal : ∀ a b, OnSpine s t a →
      (TrackCutStep cut a b ↔ PositiveSpineCutStep e f a b))
    (hab : Relation.EqvGen (TrackCutStep cut) a b) (ha : OnSpine s t a) :
    Relation.EqvGen (PositiveSpineCutStep e f) a b := by
  revert ha
  induction hab with
  | rel a b h => intro ha; exact Relation.EqvGen.rel _ _ ((hlocal a b ha).mp h)
  | refl => intro _; exact Relation.EqvGen.refl _
  | symm a b h ih =>
    intro hb
    exact Relation.EqvGen.symm _ _ (ih ((onSpine_trackCut_component_iff ht hs htop h).mpr hb))
  | trans a b c h₁ h₂ ih₁ ih₂ =>
    intro ha
    exact Relation.EqvGen.trans _ _ _ (ih₁ ha)
      (ih₂ ((onSpine_trackCut_component_iff ht hs htop h₁).mp ha))

theorem local_cut_path_to_trackCut {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {cut : TrackComponent G} {s t e f a b : OrientedEdge G}
    (hs : ¬∃g, PositiveCellStep g s) (htop : ¬∃g, PositiveCellStep t g)
    (hlocal : ∀ a b, OnSpine s t a →
      (TrackCutStep cut a b ↔ PositiveSpineCutStep e f a b))
    (hab : Relation.ReflTransGen (PositiveSpineCutStep e f) a b) (ha : OnSpine s t a) :
    Relation.ReflTransGen (TrackCutStep cut) a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hab hbc ih =>
    have hpos := Relation.ReflTransGen.mono (fun _ _ h => h.1) _ _ hab
    have hb := (onSpine_positive_path_iff ht hs htop hpos).mp ha
    exact ih.tail ((hlocal b c hb).mpr hbc)

theorem trackCutPieces_eq_pair {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {cut : TrackComponent G} {s t e f : OrientedEdge G}
    (hs : ¬∃g, PositiveCellStep g s) (htop : ¬∃g, PositiveCellStep t g)
    (hse : Relation.ReflTransGen PositiveCellStep s e) (hef : PositiveCellStep e f)
    (hft : Relation.ReflTransGen PositiveCellStep f t)
    (hlocal : ∀ a b, OnSpine s t a →
      (TrackCutStep cut a b ↔ PositiveSpineCutStep e f a b)) :
    trackCutPieces cut s t={trackCutComponent cut e,trackCutComponent cut f} := by
  have he : OnSpine s t e := ⟨hse,(Relation.ReflTransGen.single hef).trans hft⟩
  have hf : OnSpine s t f := ⟨hse.tail hef,hft⟩
  ext q
  simp only [trackCutPieces,Finset.mem_image,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨a,ha,rfl⟩
    have haFull : OnSpine s t a := (Finset.mem_filter.mp ha).2
    rw [spine_cut_partition ht hse hef hft] at ha
    rcases Finset.mem_union.mp ha with ha | ha
    · left
      apply Quotient.sound
      exact Relation.EqvGen.reflTransGen_le_eqvGen _ _ _
        (local_cut_path_to_trackCut ht hs htop hlocal
          (path_before_cut_survives hef (Finset.mem_filter.mp ha).2.2) haFull)
    · right
      apply Eq.symm
      apply Quotient.sound
      exact Relation.EqvGen.reflTransGen_le_eqvGen _ _ _
        (local_cut_path_to_trackCut ht hs htop hlocal
          (path_after_cut_survives hef (Finset.mem_filter.mp ha).2.1) hf)
  · rintro (rfl | rfl)
    · exact ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩,rfl⟩
    · exact ⟨f,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf⟩,rfl⟩

theorem trackCutPieces_card_two {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {cut : TrackComponent G} {s t e f : OrientedEdge G}
    (hs : ¬∃g, PositiveCellStep g s) (htop : ¬∃g, PositiveCellStep t g)
    (hse : Relation.ReflTransGen PositiveCellStep s e) (hef : PositiveCellStep e f)
    (hft : Relation.ReflTransGen PositiveCellStep f t)
    (hlocal : ∀ a b, OnSpine s t a →
      (TrackCutStep cut a b ↔ PositiveSpineCutStep e f a b)) :
    (trackCutPieces cut s t).card=2 := by
  have hne : trackCutComponent cut e≠trackCutComponent cut f := by
    intro heq
    have hpath := trackCut_component_to_local ht hs htop hlocal (Quotient.exact heq)
      ⟨hse,(Relation.ReflTransGen.single hef).trans hft⟩
    exact cut_step_endpoints_disconnected ht hef (Quotient.sound hpath)
  rw [trackCutPieces_eq_pair ht hs htop hse hef hft hlocal,Finset.card_pair hne]

theorem crossing_track_cut_realization {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    (c cut : TrackComponent G) (hne : c≠cut) (hcross : ComponentCrosses c cut) :
    ∃ q : SpineTransition G, ∃ s t : OrientedEdge G,
      edgeComponent q.val.1=c ∧ cutRhombus cut q.rhombus ∧
      (¬∃g, PositiveCellStep g s) ∧ (¬∃g, PositiveCellStep t g) ∧
      OnSpine s t q.val.1 ∧ (trackCutPieces cut s t).card=2 ∧
      (spineVertices s t).card=(spineVertices s q.val.1).card+(spineVertices q.val.2 t).card := by
  obtain ⟨q,hqc,hqcut,hpairs⟩ := crossing_cut_transition_pair ht c cut hne hcross
  obtain ⟨s,t,hs,htop,he,_⟩ := component_spine_iff ht q.val.1
  have hft := spine_suffix_closed ht htop he.2 q.property
  have hpairs' : ∀ p : SpineTransition G,
      edgeComponent p.val.1=edgeComponent q.val.1 ∧ cutRhombus cut p.rhombus → p=q ∨ p=q.reverse := by
    intro p hp
    exact (hpairs p).mp ⟨hp.1.trans hqc,hp.2⟩
  have hlocal : ∀ a b, OnSpine s t a →
      (TrackCutStep cut a b ↔ PositiveSpineCutStep q.val.1 q.val.2 a b) :=
    fun a b ha => trackCutStep_on_spine_iff ht cut q hqcut hpairs' he.1 (a := a) (b := b) ha
  exact ⟨q,s,t,hqc,hqcut,hs,htop,he,
    trackCutPieces_card_two ht hs htop he.1 q.property hft hlocal,
    spine_cut_edge_count ht he.1 q.property hft⟩

end Swanepoel
