module
public import Swanepoel.EulerStart
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def PennyGraph.contactGraph {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) : SimpleGraph (Fin n) where
  Adj i j := ∃ e ∈ S, s(e.val.1,e.val.2)=s(i,j)
  symm := ⟨by
    rintro i j ⟨e,he,hij⟩
    exact ⟨e,he,hij.trans Sym2.eq_swap⟩⟩
  loopless := ⟨by
    rintro i ⟨e,_,he⟩
    rcases Sym2.eq_iff.mp he with h | h <;>
      exact e.property.2.ne (h.1.trans h.2.symm)⟩

theorem PennyGraph.contactGraph_adj_iff {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G) :
    (G.contactGraph S).Adj e.val.1 e.val.2 ↔ e ∈ S := by
  constructor
  · rintro ⟨f,hf,hfe⟩
    exact (f.eq_of_unordered_eq e hfe) ▸ hf
  · intro he
    exact ⟨e,he,rfl⟩

theorem PennyGraph.contactGraph_le {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) : G.contactGraph S ≤ G.graph := by
  rintro i j ⟨e,_,he⟩
  rcases Sym2.eq_iff.mp he with h | h
  · simpa only [h.1,h.2] using e.property.2
  · simpa only [h.1,h.2] using e.property.2.symm

theorem PennyGraph.contactGraph_mono {n : ℕ} (G : PennyGraph n)
    {S T : Finset (ContactEdge G)} (hST : S ⊆ T) :
    G.contactGraph S ≤ G.contactGraph T := by
  rintro i j ⟨e,he,hij⟩
  exact ⟨e,hST he,hij⟩

theorem PennyGraph.contactGraph_empty {n : ℕ} (G : PennyGraph n) :
    G.contactGraph ∅=⊥ := by
  ext i j
  simp [PennyGraph.contactGraph]

theorem PennyGraph.contactGraph_univ {n : ℕ} (G : PennyGraph n) :
    G.contactGraph Finset.univ=G.graph := by
  apply le_antisymm (G.contactGraph_le _)
  intro i j hij
  rcases lt_or_gt_of_ne hij.ne with h | h
  · exact ⟨⟨(i,j),h,hij⟩,Finset.mem_univ _,rfl⟩
  · exact ⟨⟨(j,i),h,hij.symm⟩,Finset.mem_univ _,Sym2.eq_swap⟩

theorem PennyGraph.contactGraph_edge_count {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) : (G.contactGraph S).edgeFinset.card=S.card := by
  classical
  symm
  refine Finset.card_bij (fun e _ => s(e.val.1,e.val.2)) ?_ ?_ ?_
  · intro e he
    exact SimpleGraph.mem_edgeFinset.mpr ((G.contactGraph_adj_iff S e).mpr he)
  · intro e _ f _ hef
    exact e.eq_of_unordered_eq f hef
  · intro z hz
    induction z using Sym2.inductionOn with
    | _ i j =>
      obtain ⟨e,he,hij⟩ := SimpleGraph.mem_edgeFinset.mp hz
      exact ⟨e,he,hij⟩

def PennyGraph.contactsOf {n : ℕ} (G : PennyGraph n) (H : SimpleGraph (Fin n)) :
    Finset (ContactEdge G) := Finset.univ.filter (fun e => H.Adj e.val.1 e.val.2)

theorem PennyGraph.contactGraph_contactsOf {n : ℕ} (G : PennyGraph n)
    (H : SimpleGraph (Fin n)) (hHG : H ≤ G.graph) :
    G.contactGraph (G.contactsOf H)=H := by
  ext i j
  constructor
  · rintro ⟨e,he,hij⟩
    have ha : H.Adj e.val.1 e.val.2 := (Finset.mem_filter.mp he).2
    rcases Sym2.eq_iff.mp hij with h | h
    · simpa only [h.1,h.2] using ha
    · simpa only [h.1,h.2] using ha.symm
  · intro hij
    rcases lt_or_gt_of_ne hij.ne with h | h
    · exact ⟨⟨(i,j),h,hHG hij⟩,by simp [PennyGraph.contactsOf,hij],rfl⟩
    · exact ⟨⟨(j,i),h,hHG hij.symm⟩,by simp [PennyGraph.contactsOf,hij.symm],Sym2.eq_swap⟩

theorem PennyGraph.exists_contact_spanning_tree {n : ℕ} (G : PennyGraph n)
    (hc : G.graph.Connected) :
    ∃ T : Finset (ContactEdge G), (G.contactGraph T).IsTree ∧ T.card+1=n := by
  classical
  obtain ⟨H,hHG,hH⟩ := hc.exists_isTree_le
  refine ⟨G.contactsOf H,?_,?_⟩
  · simpa only [G.contactGraph_contactsOf H hHG] using hH
  · have hcard := hH.card_edgeFinset
    rw [← G.contactGraph_contactsOf H hHG,G.contactGraph_edge_count] at hcard
    simpa only [Fintype.card_fin] using hcard

end Swanepoel
