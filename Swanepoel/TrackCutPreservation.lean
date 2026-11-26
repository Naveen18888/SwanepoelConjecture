module
public import Swanepoel.TrackCutRealization
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem noncrossing_path_preserved {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {cut : TrackComponent G} {a b : OrientedEdge G}
    (hne : edgeComponent a≠cut) (hncross : ¬ComponentCrosses (edgeComponent a) cut)
    (hab : Relation.ReflTransGen PositiveCellStep a b) :
    Relation.ReflTransGen (TrackCutStep cut) a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hab hbc ih =>
    have hcomp : edgeComponent b=edgeComponent a := (positive_path_component hab).symm
    exact ih.tail (noncrossing_step_preserved ht (by simpa only [hcomp] using hne)
      (by simpa only [hcomp] using hncross) hbc)

theorem noncrossing_trackCutPieces_eq_singleton {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {cut : TrackComponent G} {s t : OrientedEdge G}
    (hne : edgeComponent s≠cut) (hncross : ¬ComponentCrosses (edgeComponent s) cut)
    (hst : Relation.ReflTransGen PositiveCellStep s t) :
    trackCutPieces cut s t={trackCutComponent cut s} := by
  ext q
  simp only [trackCutPieces,Finset.mem_image,Finset.mem_singleton]
  constructor
  · rintro ⟨a,ha,rfl⟩
    apply Eq.symm
    apply Quotient.sound
    exact Relation.EqvGen.reflTransGen_le_eqvGen _ _ _
      (noncrossing_path_preserved ht hne hncross (Finset.mem_filter.mp ha).2.1)
  · intro hq
    subst q
    exact ⟨s,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Relation.ReflTransGen.refl,hst⟩,rfl⟩

theorem noncrossing_track_cut_realization {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    (c cut : TrackComponent G) (hne : c≠cut) (hncross : ¬ComponentCrosses c cut) :
    ∃ s t : OrientedEdge G,
      edgeComponent s=c ∧ (¬∃g, PositiveCellStep g s) ∧ (¬∃g, PositiveCellStep t g) ∧
      Relation.ReflTransGen PositiveCellStep s t ∧
      (∀ a, edgeComponent a=c ↔ OnUnorientedSpine s t a) ∧
      (trackCutPieces cut s t).card=1 := by
  obtain ⟨s,t,hs,htop,he,hall⟩ := component_spine_iff ht c.out
  have hroot : edgeComponent c.out=c := Quotient.out_eq c
  have hsc : edgeComponent s=c := (positive_path_component he.1).trans hroot
  have hst := he.1.trans he.2
  refine ⟨s,t,hsc,hs,htop,hst,?_,?_⟩
  · intro a
    simpa only [hroot] using hall a
  · rw [noncrossing_trackCutPieces_eq_singleton ht (by simpa only [hsc] using hne)
      (by simpa only [hsc] using hncross) hst,Finset.card_singleton]

end Swanepoel
