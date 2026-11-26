module
public import Swanepoel.SpineCounting
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem card_eq_mul_of_constant_fibers {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (S : Finset α) (f : α → β) (k : ℕ)
    (h : ∀ b, (S.filter (fun a => f a=b)).card=k) :
    S.card=Fintype.card β*k := by
  classical
  calc
    S.card=∑ b : β, (S.filter (fun a => f a=b)).card :=
      Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    _ = ∑ _ : β, k := Finset.sum_congr rfl (fun b _ => h b)
    _ = Fintype.card β*k := by simp

theorem spine_source_count {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) :
    ((Finset.univ : Finset (OrientedEdge G)).filter SpineSource).card=
      2*Fintype.card (TrackComponent G) := by
  have h := card_eq_mul_of_constant_fibers
    ((Finset.univ : Finset (OrientedEdge G)).filter SpineSource) edgeComponent 2
    (fun c => by simpa only [Finset.filter_filter] using component_source_count ht c)
  simpa only [Nat.mul_comm] using h

def orientedEdgeMap {n : ℕ} {G : PennyGraph n} (e : OrientedEdge G) : G.graph.edgeSet :=
  ⟨s(e.val.1,e.val.2),e.property⟩

theorem oriented_edge_fiber_count {n : ℕ} (G : PennyGraph n) (z : G.graph.edgeSet) :
    ((Finset.univ : Finset (OrientedEdge G)).filter (fun e => orientedEdgeMap e=z)).card=2 := by
  rcases z with ⟨z,hz⟩
  revert hz
  refine Sym2.inductionOn z ?_
  intro i j hij
  change G.graph.Adj i j at hij
  let e : OrientedEdge G := ⟨(i,j),hij⟩
  let f : OrientedEdge G := reverseEdge e
  have hef : e≠f := by
    intro h
    exact hij.ne (congrArg (fun x : OrientedEdge G => x.val.1) h)
  have hset : ((Finset.univ : Finset (OrientedEdge G)).filter
      (fun x => orientedEdgeMap x=⟨s(i,j),hij⟩))={e,f} := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      have hv := congrArg Subtype.val h
      rcases Sym2.eq_iff.mp hv with h | h
      · exact Or.inl (Subtype.ext (Prod.ext h.1 h.2))
      · exact Or.inr (Subtype.ext (Prod.ext h.1 h.2))
    · rintro (rfl | rfl)
      · rfl
      · apply Subtype.ext
        exact Sym2.eq_iff.mpr (Or.inr ⟨rfl,rfl⟩)
  rw [hset,Finset.card_pair hef]

theorem oriented_edge_count {n : ℕ} (G : PennyGraph n) :
    Fintype.card (OrientedEdge G)=2*G.edgeCount := by
  have h := card_eq_mul_of_constant_fibers
    (Finset.univ : Finset (OrientedEdge G)) orientedEdgeMap 2
    (oriented_edge_fiber_count G)
  simpa only [Finset.card_univ,Nat.mul_comm,PennyGraph.edgeCount,
    SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] using h

abbrev SpineTransition {n : ℕ} (G : PennyGraph n) :=
  {p : OrientedEdge G × OrientedEdge G // PositiveCellStep p.1 p.2}

noncomputable instance {n : ℕ} (G : PennyGraph n) : Fintype (SpineTransition G) :=
  Fintype.ofFinite _

theorem transition_count_add_sources {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) :
    Fintype.card (SpineTransition G)+
      ((Finset.univ : Finset (OrientedEdge G)).filter SpineSource).card=
        Fintype.card (OrientedEdge G) := by
  let target : SpineTransition G → {e : OrientedEdge G // ¬ SpineSource e} :=
    fun p => ⟨p.val.2,fun hs => hs ⟨p.val.1,p.property⟩⟩
  have hi : Function.Injective target := by
    intro p q hpq
    have he : p.val.2=q.val.2 := congrArg Subtype.val hpq
    have hq : PositiveCellStep q.val.1 p.val.2 := by rw [he]; exact q.property
    have hs := positive_step_injective ht p.property hq
    exact Subtype.ext (Prod.ext hs he)
  have hs : Function.Surjective target := by
    rintro ⟨e,he⟩
    obtain ⟨f,hf⟩ := not_not.mp he
    exact ⟨⟨(f,e),hf⟩,rfl⟩
  have hc := Fintype.card_congr (Equiv.ofBijective target ⟨hi,hs⟩)
  have hsub := Fintype.card_subtype_le (α := OrientedEdge G) SpineSource
  have hcomp := Fintype.card_subtype_compl (α := OrientedEdge G) SpineSource
  have hsource : Fintype.card {e : OrientedEdge G // SpineSource e}=
      ((Finset.univ : Finset (OrientedEdge G)).filter SpineSource).card :=
    Fintype.card_of_subtype _ (by intro e; simp)
  simp only [← Nat.card_eq_fintype_card] at hc hcomp hsub hsource ⊢
  omega

theorem transition_track_count {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) :
    Fintype.card (SpineTransition G)+2*Fintype.card (TrackComponent G)=2*G.edgeCount := by
  simpa only [spine_source_count G ht,oriented_edge_count G] using
    transition_count_add_sources G ht

end Swanepoel
