module
public import Swanepoel.TrackCutPreservation
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

abbrev TrackCutOther {n : ℕ} {G : PennyGraph n} (cut : TrackComponent G) :=
  {c : TrackComponent G // c≠cut}

noncomputable instance {n : ℕ} {G : PennyGraph n} (cut : TrackComponent G) :
    Fintype (TrackCutOther cut) := Fintype.ofFinite _

theorem track_cut_spine_exists {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    (c cut : TrackComponent G) (hne : c≠cut) : ∃ s t : OrientedEdge G,
      edgeComponent s=c ∧ (¬∃g, PositiveCellStep g s) ∧ (¬∃g, PositiveCellStep t g) ∧
      Relation.ReflTransGen PositiveCellStep s t ∧
      (trackCutPieces cut s t).card=(if ComponentCrosses c cut then 2 else 1) := by
  by_cases hcross : ComponentCrosses c cut
  · obtain ⟨q,s,t,hqc,_,hs,htop,he,hcount,_⟩ := crossing_track_cut_realization ht c cut hne hcross
    refine ⟨s,t,(positive_path_component he.1).trans hqc,hs,htop,he.1.trans he.2,?_⟩
    simpa only [ite_eq_left hcross] using hcount
  · obtain ⟨s,t,hsc,hs,htop,hst,_,hcount⟩ := noncrossing_track_cut_realization ht c cut hne hcross
    exact ⟨s,t,hsc,hs,htop,hst,by simpa only [ite_eq_right hcross] using hcount⟩

theorem trackCutOther_card {n : ℕ} {G : PennyGraph n} (cut : TrackComponent G) :
    Fintype.card (TrackCutOther cut)+1=Fintype.card (TrackComponent G) := by
  have hc : Fintype.card (TrackCutOther cut)=
      ((Finset.univ : Finset (TrackComponent G)).erase cut).card :=
    Fintype.card_of_subtype _ (by intro c; simp)
  rw [hc]
  simpa only [Finset.card_univ] using Finset.card_erase_add_one (Finset.mem_univ cut)

theorem track_cut_piece_count {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    (cut : TrackComponent G) :
    ∃ s t : TrackCutOther cut → OrientedEdge G,
      (∀ c, edgeComponent (s c)=c.val ∧
        (¬∃g, PositiveCellStep g (s c)) ∧ (¬∃g, PositiveCellStep (t c) g) ∧
        Relation.ReflTransGen PositiveCellStep (s c) (t c)) ∧
      (∑ c : TrackCutOther cut, (trackCutPieces cut (s c) (t c)).card)+1=
        Fintype.card (TrackComponent G)+
          ((Finset.univ : Finset (TrackCutOther cut)).filter (fun c => ComponentCrosses c.val cut)).card := by
  classical
  have hex := fun c : TrackCutOther cut => track_cut_spine_exists ht c.val cut c.property
  choose s t h using hex
  refine ⟨s,t,fun c => ⟨(h c).1,(h c).2.1,(h c).2.2.1,(h c).2.2.2.1⟩,?_⟩
  have hsum : (∑ c : TrackCutOther cut, (trackCutPieces cut (s c) (t c)).card)=
      Fintype.card (TrackCutOther cut)+
        ((Finset.univ : Finset (TrackCutOther cut)).filter (fun c => ComponentCrosses c.val cut)).card := by
    calc
      _ = ∑ c : TrackCutOther cut, (if ComponentCrosses c.val cut then 2 else 1) :=
        Finset.sum_congr rfl (fun c _ => (h c).2.2.2.2)
      _ = ∑ c : TrackCutOther cut, (1+(if ComponentCrosses c.val cut then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro c _
        split_ifs <;> norm_num
      _ = _ := by
        have hcount :
            ((Finset.univ : Finset (TrackCutOther cut)).filter
              (fun c => ComponentCrosses c.val cut)).card=
            ∑ c : TrackCutOther cut, (if ComponentCrosses c.val cut then 1 else 0) := by
          simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
        rw [Finset.sum_add_distrib,← hcount]
        simp
  rw [hsum]
  have hc := trackCutOther_card cut
  omega

end Swanepoel
