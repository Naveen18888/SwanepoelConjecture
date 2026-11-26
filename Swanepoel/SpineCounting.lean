module
public import Swanepoel.GeometricCounting
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

noncomputable instance spineEdgeFintype {n : ℕ} (G : PennyGraph n) :
    Fintype (OrientedEdge G) := Fintype.ofFinite _

def SpineSource {n : ℕ} {G : PennyGraph n} (e : OrientedEdge G) : Prop :=
  ¬ ∃ f, PositiveCellStep f e

theorem positive_path_vector_eq {n : ℕ} {G : PennyGraph n} {e f : OrientedEdge G}
    (h : Relation.ReflTransGen PositiveCellStep e f) : carriedVector e=carriedVector f := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact ih.trans h.to_cellStep.vector_eq

theorem source_path_eq {n : ℕ} {G : PennyGraph n} {e f : OrientedEdge G}
    (hf : SpineSource f) (h : Relation.ReflTransGen PositiveCellStep e f) : e=f := by
  rcases h.cases_tail with h | ⟨g,_,hgf⟩
  · exact h.symm
  · exact False.elim (hf ⟨g,hgf⟩)

theorem spine_opposite_sources_ne {n : ℕ} {G : PennyGraph n} {s t : OrientedEdge G}
    (h : Relation.ReflTransGen PositiveCellStep s t) : s≠reverseEdge t := by
  intro he
  have hv := positive_path_vector_eq h
  rw [he,reverseEdge_vector] at hv
  have hz : carriedVector t=0 := by
    ext i
    have hi := congrArg (fun x : Plane => x i) hv
    change -(carriedVector t i)=carriedVector t i at hi
    change carriedVector t i=0
    linarith
  have hn := carriedVector_norm t
  rw [hz,norm_zero] at hn
  norm_num at hn

theorem component_sources {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    (c : TrackComponent G) : ∃ s t : OrientedEdge G, s≠t ∧
      ∀ e, (SpineSource e ∧ edgeComponent e=c) ↔ e=s ∨ e=t := by
  obtain ⟨s,t,hs,htop,he,hall⟩ := component_spine_iff ht c.out
  have hroot : edgeComponent c.out=c := Quotient.out_eq c
  have hsc : edgeComponent s=c := (positive_path_component he.1).trans hroot
  have htc : edgeComponent (reverseEdge t)=c :=
    (reverse_component t).symm.trans ((positive_path_component he.2).symm.trans hroot)
  have hrt : SpineSource (reverseEdge t) := by
    rintro ⟨g,hg⟩
    have hh := hg.reverse
    simp only [reverseEdge_involutive] at hh
    exact htop ⟨reverseEdge g,hh⟩
  refine ⟨s,reverseEdge t,spine_opposite_sources_ne (he.1.trans he.2),?_⟩
  intro e
  constructor
  · rintro ⟨hsource,hc⟩
    rcases (hall e).mp (hc.trans hroot.symm) with hp | hp
    · exact Or.inl (source_path_eq hsource hp.1).symm
    · exact Or.inr (source_path_eq hsource hp.1).symm
  · rintro (rfl | rfl)
    · exact ⟨hs,hsc⟩
    · exact ⟨hrt,htc⟩

theorem component_source_count {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    (c : TrackComponent G) :
    ((Finset.univ : Finset (OrientedEdge G)).filter
      (fun e => SpineSource e ∧ edgeComponent e=c)).card=2 := by
  obtain ⟨s,t,hne,hall⟩ := component_sources ht c
  have hset : ((Finset.univ : Finset (OrientedEdge G)).filter
      (fun e => SpineSource e ∧ edgeComponent e=c))={s,t} := by
    ext e
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,
      Finset.mem_singleton] using hall e
  rw [hset,Finset.card_pair hne]

end Swanepoel
